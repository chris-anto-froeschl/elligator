# A Formalization of the Elligator Family of Uniform Encodings to Elliptic Curves

Draft for submission to the *Annals of Formalized Mathematics* (AFM, episciences.org).

## On the template

AFM does not publish an official style file -- their Instructions
for Authors say so directly: "we do not publicly provide our
official style file, so please submit papers using your preferred
class." (https://afm.episciences.org/page/instructions-for-authors)

So this uses `amsart`, the standard AMS article class most
mathematicians default to, with no custom package on top. `amsart`'s
own fields cover everything AFM asks for in the body of the paper:
`\subjclass` for the MSC classification, `\keywords`, `\address` /
`\email` for contact information, and the standard `abstract`
environment. `hyperref` is loaded with no options, so links behave
however your LaTeX distribution's default is (typically boxed, not
colored text).

What's deliberately **not** here: a fabricated journal
name/volume/DOI header or "Received/Accepted" dates. Published AFM
papers do carry those, but that's typesetting AFM applies once a
paper is accepted (comparable to how Elsevier stamps a masthead onto
the final version of an accepted paper) -- not something a submitted
manuscript needs to reproduce itself.

Submission itself does not go through a journal portal: AFM requires
the manuscript to be deposited first on HAL, arXiv, or Zenodo,
referencing an open, referee-accessible code artifact (the CSLib
PR/repo), with the paper explicitly linking main results to specific
code. See the Instructions for Authors page for the current
submission procedure.

## Build

    make            # produces main.pdf
    make watch      # rebuild on change (latexmk -pvc)
    make clean      # remove intermediate files
    make cleanall   # also remove main.pdf

## Layout

    main.tex                title/author/subjclass/keywords/abstract, \input list
    sections/*.tex           one file per section
    refs.bib                 bibliography (bibliographystyle: alpha)
