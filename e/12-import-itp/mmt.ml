needs "update_database.ml";;

let skipexport =
  List.map fst (List.filter (fun (a,b) -> b>6) (List.map (fun (a,b) -> (a,(length o type_vars_in_term o concl)b)) !theorems));;
let toexport = List.filter (fun (a,b) -> not (List.mem a skipexport)) !theorems;;

(*⟺*)
(* ⊆‍ ∈*)

let rxpprim = Str.regexp "'";;
let rxpperc = Str.regexp "%";;

let escaped = function
  "/\\" -> "∧"
| "\\/" -> "∨"
| "==>" -> "⟹"
| "fun" -> "⇒"
| "!" -> "∀"
| "?" -> "∃"
| "~" -> "¬"
| "@" -> "ε"
| "<=" -> "≤"
| ">=" -> "≥"
| "F" -> "⊥"
| "T" -> "⊤"
| "?!" -> "∃!"
| "lambda" -> "Λ"
| s -> Str.global_replace rxpprim "_'" (Str.global_replace rxpperc "_" s);;

let escaped2 s =
  let s = if s.[0] = '_' then " " ^ s else s in
  let s = if s.[String.length s - 1] = '_' then s ^ " " else s in
  s;;

let first_q_under x = if x.[0] <> '?' then x else "?_" ^ (String.sub x 1 (String.length x - 1));;

let os s = Format.print_string s;;
let ose s = Format.print_string (escaped2 (first_q_under (escaped s)));;
let ob () = Format.open_vbox 2;;
let cb () = Format.close_box ();;
let nl () = Format.force_newline ();;


let rec omdoc_type = function
    Tyvar x -> ose x
  | Tyapp (s, []) -> ose s
  | Tyapp ("fun", [l; r]) -> os "("; omdoc_type l; ose "fun"; omdoc_type r; os ")"
  | Tyapp (s, l) -> os "("; ose s; List.iter (fun ty -> os " "; omdoc_type ty) l; os ")"
;;

let inst_const (n, ty) =
  let gty = get_const_type n in
  let inst = type_match gty ty [] in
  let rinst = map (fun (a, b) -> (b, a)) inst in
  let tvs = tyvars gty in
  map (fun x -> assoc x rinst) tvs
;;

(* TODO: Type variables and term variables can clash *)
let omdoc_const (s, t) =
  match inst_const (s, t) with
    [] -> ose s
  | l -> os "("; ose s; List.iter (fun ty -> os " "; omdoc_type ty) l; os ")"
;;

let omdoc_var_w_type (x, ty) =
  ose x; os ": term "; omdoc_type ty
;;

let rec omdoc_term tm =
  try
    let l,r = dest_eq tm in
    os "("; omdoc_term l; os "="; omdoc_term r; os ")"
  with Failure _ ->
  match tm with
    Comb (l, r) -> os "("; omdoc_term l; os " ' "; omdoc_term r; os ")"
  | Var (x, t) -> ose x
  | Const (s, t) -> omdoc_const (s, t)
  | Abs (v, t) -> os "(λ["; omdoc_var_w_type (dest_var v); os "] "; omdoc_term t; os ")"
;;

let omdoc_quant tm =
  match frees tm with
    [] -> os "⊦ "; omdoc_term tm
  | l -> List.iter (fun x -> os "{"; omdoc_var_w_type (dest_var x); os "}") l;
      os "⊦ "; omdoc_term tm
;;

let omdoc_prop tm =
  match type_vars_in_term tm with
    [] -> omdoc_quant tm
  | l -> List.iter (fun x -> os "{"; ose (dest_vartype x); os "}") l; omdoc_quant tm
;;

let omdoc_thm (name, thm) =
  ose name; os " : "; omdoc_prop (concl thm)
;;

let rxpbtick = Str.regexp "`";;
let thy = ref "";;

let basename str =
  let l = hd (rev (Str.split rxpslash str)) in
  String.sub l 0 (String.length l - 3)
;;

let maybe_new_theory file =
  let file = basename file in
  if file <> !thy then begin
    (if !thy <> "" then (os "\030"; cb (); nl (); os "\029"; nl ()));
    ob (); os "theory "; os file; os " : ?HOL ="; nl ();
    (if !thy <> "" then (os "include ?"; os !thy; os "\030"; nl ()));
    thy := file
  end else (os "\030"; nl ())
;;

let mmt_ctype cname =
  let ty = get_const_type cname in
  let tvs = tyvars ty in
  ose cname; os " : "; List.iter (fun tv -> os "{"; ose (dest_vartype tv); os "}") tvs;
  os " term "; omdoc_type ty
;;

let needs_rename s =
  try ignore (get_const_type s); true with _ ->
  try ignore (get_type_arity s); true with _ -> false
;;

let process_line l =
  if l.[0] = '-' then begin
    if String.length l > 1 then
      if l.[1] = 'c' then begin
        let [file; cname] = Str.split rxpbtick (String.sub l 2 (String.length l - 2)) in
        maybe_new_theory file;
        mmt_ctype cname
      end else if l.[1] = 't' then begin
        let [file; tname; abs; rep] = Str.split rxpbtick (String.sub l 2 (String.length l - 2)) in
        maybe_new_theory file;
        let ari = get_type_arity tname in
        ose tname; os " : "; List.iter (fun _ -> os "holtype → ") (replicate () ari); os "holtype"; os "\030"; nl ();
        mmt_ctype abs; os "\030"; nl ();
        mmt_ctype rep
      end
  end else begin
    let [file; th] = Str.split rxpbtick l in
    maybe_new_theory file;
    let thr = if needs_rename th then th ^ "_renamed" else th in
    if not (List.mem th skipexport) then
      omdoc_thm (thr, List.assoc th !theorems)
  end;;

let rec iter2 f = function
  [] -> ()
| [(h,n)] -> f h
| (h1,n1) :: (h2,n2) :: t ->
    if n1 <> n2 then (f h1; iter2 f ((h2, n2) :: t))
    else (f h2; iter2 f ((h1, n1) :: t))
;;

let omdoc_all () =
  thy := "";
  let rxpspace = Str.regexp " " in
  let rxpslash = Str.regexp "/" in
  let oc = open_out "hollight.mmt" in
  os "namespace http://latin.omdoc.org/foundations/hollight\029"; nl ();
  Format.set_formatter_out_channel oc;
  let l = strings_of_file "facts.lst" in
  let l2 = List.map (fun s -> let [t;n] = Str.split rxpspace s in (t,n)) l in
  iter2 process_line l2;
  cb (); nl (); os "\029";
  Format.print_flush ();
  Format.set_formatter_out_channel stdout;
  close_out oc;
;;

