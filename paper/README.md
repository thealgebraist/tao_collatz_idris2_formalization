# A self-contained proof of the central theorem (LaTeX)

`central-theorem.pdf` is a step-by-step, self-contained proof of the central
theorem of `taocollatz.pdf` — *Almost all Collatz orbits attain almost bounded
values* (Theorem 1.3) — written to track the Idris2 formalization in
`../TaoCollatz/`.

Every definition, axiom, and lemma carries a **margin tag** naming the
corresponding Idris2 declaration:

* red **AXIOM** tags mark the two explicit hypotheses / analytic inputs
  (`OddThresholdSystem`, `firstPassageAnalyticInput`);
* blue **LEMMA** and green **DEF** tags mark the proved lemmas and definitions.

**Handwritten** annotations appear in the margins and inline. Each is authored
as an SVG in `handwritten/*.svg` (text set in the DkgHandwriting font) and
rendered to PDF with `rsvg-convert`; the LaTeX document embeds those PDFs.

## `matrix-proof.pdf` --- the matrix-only proof

`matrix-proof.pdf` (source `matrix-proof.tex`) is a **matrix-only**,
self-contained proof of the same Theorem 1.3: every part of the argument is laid
out purely as a matrix/table --- a definitions matrix, the reduction chain and
its dependency (adjacency) matrix, the two matrices proving the odd-part step
(R4), the ``almost all'' density-algebra matrix, and a final proved-vs-assumed
matrix. Each row cites the exact Idris2 declaration it corresponds to. Build
with `tectonic matrix-proof.tex` (or `pdflatex matrix-proof.tex`); it needs only
standard packages (`amsmath`, `array`, `longtable`, `booktabs`, `xcolor`).

## Rebuild

```
./make-handwritten.sh                 # regenerate handwritten/*.pdf from *.svg
pdflatex central-theorem.tex          # run twice for cross-references
pdflatex central-theorem.tex
```

Requires: a LaTeX installation (marginnote, tikz, tcolorbox, seqsplit, …),
`rsvg-convert` (librsvg2-bin), and a handwriting font (fonts-dkg-handwriting).
