<?php include('header.php')?>

<div class="side_bar">
 <div class="sub_menu">
  <div>Contents</div>
  <a href="#descr">description</a>
  <a href="#code">source code</a>
  <a href="#experiments">experiments</a>
 </div>
</div>

<div class="content">

<h3><a name="descr"></a>Description</h3>

<p>
This website hosts accompanying material for the paper 
<a href="https://doi.org/10.1007/978-3-031-63498-7_6">Tableaux for Automated Reasoning in Dependently-Typed Higher-Order-Logic</a>
by J. Niederhauser, C. Brown and C. Kaliszyk which has
been published at IJCAR 2024. The original version of Lash can be found
<a href="http://grid01.ciirc.cvut.cz/~chad/ijcar2022lash/">here</a>.
</p>

<br /><br />

<h3><a name="source"></a>Source code</h3>
You can download the source code including problem files and scripts
for reproducing the experimental results <a href="lash-dhol.zip">here</a>. 

<br /><br />

<h3><a name="experiments"></a>Experiments</h3>

We investigated a set of 34 TPTP DHOL problems which together prove that
list reversal is an involution on dependently-typed lists.  The results compare 
the performance of Lash in a DHOL-only mode with Lash in an erasure-only mode as 
well as all other HOL provers available on SystemOnTPTP on the translated problems.

<ul>
<li>
<a href="results/results_lash_native.txt">results</a> for the DHOL-only mode of Lash
</li>
<li>
<a href="results/results_lash_erasure.txt">results</a> for the erasure-only mode of Lash
</li>
<li>
<a href="results/results_others.txt">results</a> for available HOL provers on SystemOnTPTP
</li>
</ul>

<?php include('footer.php') ?>
