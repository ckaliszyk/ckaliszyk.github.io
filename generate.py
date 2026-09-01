#!/usr/bin/env python3

import bibtexparser

START = 2024

KEYS = {
   "inproceedings": ("author", "title", "booktitle"),
   "article"      : ("author", "title", "journal"),
   "incollection" : ("author", "title", "booktitle"),
   "proceedings"  : ("editor", "title", "series")
}

REPLACE = {
   r"\v{c}": "č",
   r"\v{r}": "ř",
   r"\'{\i}": "í",
   r'\"{a}': "ä",
   r"\k{a}": "ą",
   r"\c{c}": "ç",
   r'\"{u}': "ü",
   r"\v{s}": "š",
   r"\'{a}": "á",
   r"\L{}": "Ł",
   r"\'{y}": "ý",
   r"\r{u}": "ů",
}

OUT = "pubs.html"
BIBOUT = "bib.html"

BIBHEADER = """
<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN">
<html><head><title>ERC Project Smart - Publications</title>
<meta http-equiv="content-type" content="text/html; charset=UTF-8">
</head><body><pre>

"""

BIBFOOTER = """
</pre></body></html>

"""

def title(s):
   s = s.replace("\n"," ").replace("{","").replace("}","")
   s = '   <div class="title">%s</div>' % s
   return s + "\n"

def author(s):
   s = s.replace("\n"," ")
   for char in REPLACE:
      s = s.replace(char, REPLACE[char])
   if "\\" in s:
      print("WARNING: Unknown control sequence in: %s" % s)
   s = s.replace("{","").replace("}","")
   s = '   <div class="author">%s</div>' % s
   return s + "\n"

def book(s, year):
   s = s.replace("\n"," ")
   s = s.replace("{","").replace("}","")
   if year not in s:
      s = "%s, %s" % (s, year)
   s = '   <div class="conf">%s</div>' % s
   return s + "\n"

def links(entry):
   s = ""
   s += '      <a href="bib.html#%s">BibTeX</a>\n' % entry["ID"]
   if "url" in entry:
      s += '      <a href="%s">Publisher</a>\n' % entry["url"].replace(r"\_", "_")
   elif "doi" in entry:
      s += '      <a href="https://doi.org/%s">Publisher</a>\n' % entry["doi"].replace(r"\_", "_")
   if "arxivurl" in entry:
      s += '      <a href="%s">arXiv</a>\n' % entry["arxivurl"]
   s += '      <a href="docs/%s/%s.pdf">preprint</a>\n' % (str(entry["year"])[-2:], entry["ID"])
   s = '   <div class="links">\n%s   </div>' % s
   return s + "\n"

def format(entry, keys, out):
   (author0, title0, book0) = keys
   out.write('<a class="anchor" name="%s"></a>\n' % entry["ID"])
   out.write('<div class="pub">\n')
   out.write(title(entry[title0]))
   out.write(author(entry[author0]))
   out.write(book(entry[book0], entry["year"]))
   out.write(links(entry))
   out.write('</div>\n')

# parse all enrties
with open('all.bib') as f:
    db = bibtexparser.load(f)

# sort the entries by year (skip before `START`)
year = {}
for entry in db.entries:
   y = int(entry["year"])
   if y < START:
      continue
   if y not in year:
      year[y] = []
   year[y].append(entry)

writer = bibtexparser.bwriter.BibTexWriter()

out = open(OUT, "w")
bibout = open(BIBOUT, "w")
bibout.write(BIBHEADER)
out.write(open("HEADER").read())
for y in sorted(year, reverse=True):
   #print("XXX", y, len(year[y]))
   out.write("\n<h2>%s</h2>\n\n" % y)
   for entry in year[y]:
      #print(title(entry['title']))
      #print(entry["ENTRYTYPE"])
      #print(entry["author"])
      format(entry, KEYS[entry["ENTRYTYPE"]], out)
      #bibtexparser.dumps([entry])
      bibout.write('<a name="%s"></a>\n' % entry["ID"])
      bibout.write(writer._entry_to_bibtex(entry)+"\n")
out.write(open("FOOTER").read())
out.close()
bibout.write(BIBFOOTER)
bibout.close()

print(f"File {OUT} generated.")
print(f"File {BIBOUT} generated.")



