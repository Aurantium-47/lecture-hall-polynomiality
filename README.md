# Signed Dyck paths and Lecture Hall polynomiality

This repository contains a proof that every term of Katthän's Lecture Hall sequence is a polynomial, for the intended definition in arXiv:1809.01377v1, Conjecture 3.4. The sequence is identified explicitly with a specialization of the Stieltjes–Rogers polynomials, using signed Dyck-path weights.

The specific identification, together with the Toeplitz-to-Hankel conversion and uniqueness of the defining recurrence, is the mathematical contribution presented here. The underlying continued-fraction and Hankel identities are classical; the relevant general results are credited to Flajolet and to Sokal's exposition. No claim of priority for this specific application is made.

## Statement

For the upper-triangular Toeplitz matrix
\[
M(P)_{r,c}=
\begin{cases}
-P_{c-r+1},&c\ge r,\\
0,&c<r,
\end{cases}
\]
define
\[
E_i(P)=-
\det M(P)_{\{1,\ldots,\lceil i/2\rceil\},
\{\lfloor i/2\rfloor+1,\ldots,i\}}.
\]
The Lecture Hall sequence is the unique rational-function sequence satisfying
\[
E_i(\ell)=\prod_{j=1}^{i}y_j^{\,i+1-j}\qquad(i\ge1).
\]

Let \(\mu_n\) be the weight sum of Dyck paths of length \(2n\), with each up-step weighted \(1\) and each down-step from height \(h\) weighted
\[
\alpha_h=\varepsilon_h y_hy_{h+1},\qquad
\varepsilon_h=
\begin{cases}
-1,&h\ge4\text{ is even},\\
1,&\text{otherwise}.
\end{cases}
\]
Then
\[
\ell_{n+1}=y_1\mu_n\qquad(n\ge0).
\]
The path sum is finite, so \(\ell_i\in\mathbb Z[y_1,\ldots,y_i]\) for every \(i\ge1\).

## Source interpretation

The original paper's page 3 prints the column set starting at \(\lfloor i/2\rfloor\), giving one more column than row. The definition above starts it at \(\lfloor i/2\rfloor+1\). This is supported by the same paragraph's description of the maximal top-aligned square block without triangular zeros, the four determinants in Example 3.2, and the column convention in Definition 4.1.

The displayed formula for \(\ell_4\) in Example 3.2 also contains an inconsistent final monomial. The defining equations instead give
\[
\ell_4=y_1^2y_2^3(y_1+y_3)^2+y_1^2y_2^2y_3^2y_4,
\]
which agrees with the table in Section 6 and the expansion in Example 4.5. These interpretations are explained in the paper.

The result concerns Conjecture 3.4. It does not establish the SAGBI and initial-algebra assertions of Conjecture 4.2.

## Files

| File | Contents |
| --- | --- |
| main.tex | English proof manuscript |
| main.pdf | Compiled manuscript |
| verify.py | Exact finite verification script |
| verification.json | Recorded verification results and their finite scope |
| requirements.txt | Python dependencies |
| SUMMARY_ZH.md | Chinese summary |
| REFERENCES.md | Primary references and their roles |
| RIGHTS.md | Source attribution, external dependencies, and reuse status |
| PUBLIC_FILES.txt | Exact release file list |
| SHA256SUMS.txt | SHA-256 hashes of release files other than the hash file itself |

## Reproduce the checks

The recorded run used Python 3.8.3 and SymPy 1.6.1. The script uses Python 3.8 syntax, and requirements.txt pins the SymPy version used for these results. Other interpreter/dependency combinations have not been validated. From this directory:

~~~sh
python -m pip install -r requirements.txt
python verify.py
~~~

The computational checks concern finitely many indices. The all-index conclusion follows from the mathematical proof, not from extrapolating those checks. Consult the script and verification.json for the precise checks and bounds.

## Build the paper

With a LaTeX installation providing pdflatex:

~~~sh
pdflatex main.tex
pdflatex main.tex
~~~

The second run resolves cross-references.

## References and attribution

The three primary references are Katthan2018, Sokal2023, and Flajolet1980, listed in REFERENCES.md. In particular, Sokal's Theorem 9.1(b) gives the Dyck-path interpretation and Theorem 9.5(b,c) gives the two Hankel factorizations used here. The application to Katthän's particular sequence requires the explicit signed specialization and the defining-equation check supplied in the manuscript.

## AI assistance

This work was completed with AI assistance.

