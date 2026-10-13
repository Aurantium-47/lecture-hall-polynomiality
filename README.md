# Lecture Hall polynomiality and SAGBI extensions

**Extension author: Aurantium.** This edition adds the [SAGBI and toric-degeneration extension](extensions/LectureHall_extensions.pdf) to the unchanged [polynomiality manuscript](main.pdf). Its baseline is the corrected [v0.1.1 release](https://github.com/Aurantium-47/lecture-hall-polynomiality/releases/tag/v0.1.1), commit `f6e01a2697549781bf15facf86c6f17184facfaf`. The baseline proof, PDF, verifier, recorded output, and dependency file are byte-identical to that release. This extension edition does not replace the historical release.

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

The baseline manuscript concerns Conjecture 3.4. Its separate composition coefficient formula and exact count of `2^(i-2)` nonzero monomials in `ell_i` for `i>=2` remain part of the baseline results. Its corrected specialization remark only says that stepwise division cannot be applied directly where a divisor vanishes; it makes no claim about nonuniqueness of the complete specialized system.

## Extension statements and limits

For every `n>=1` and every field `k`, let `A_n(k)=k[ell_1,...,ell_n]` in independent variables, with degree-lexicographic order `y_1>...>y_n`. Let

```text
L_n = {e in Z^n : e_1/n >= e_2/(n-1) >= ... >= e_n >= 0}.
```

The extension proves `in_deglex A_n(k)=k[L_n]`. The `2^(n-1)` negative top-row Toeplitz minors `ell_S`, indexed by subsets of `[n-1]`, form a minimal monic SAGBI basis. Their leading exponents are precisely the Hilbert basis of `L_n`. Theorem 1.2 and Proposition 4.1 give the specific subset-to-leading-exponent map and its explicit inverse through Frobenius coordinates. These address Katthän's Conjecture 4.2 and Problem 5.1 under the disclosed square-minor interpretation.

Theorem 7.1 constructs a finitely generated `Z[t]`-algebra that is free as a module with an **infinite-rank** basis. Its fibers are `A_n(Z)` at `t=1` and `Z[L_n]` at `t=0`; after inverting `t` it becomes the trivial family, and base change to any field preserves the construction. The proof includes the strict weight decrease needed for multiplication. Finite generation as an algebra does not mean finite rank as a module.

The generic Schur-moment leading-term recursion and the equal-leading-growth argument are also proved in the extension. Classical Hankel/Jacobi–Trudi identities, the Lecture Hall generating series, and the baseline polynomiality result are not claimed as new extension results. No worldwide-priority, human peer-review, or formal-verification claim is made.

The source's Examples 4.4–4.5 also contain extra `-E_i` signs inconsistent with direct Definition 4.1; the minor definition and its displayed matrices determine the signs used here. This is a disclosed interpretation, not an author-issued erratum. The theorems concern independent indeterminates. Numerical specialization need not preserve algebraic independence or a SAGBI basis; uniqueness of the complete defining system at vanishing divisors is not addressed.

## Reproduce the extension records

The extension requires **Python 3.10+ and SymPy 1.14.0**, as pinned in `extensions/requirements.txt`. Keep this environment separate from the baseline's Python 3.8.3 / SymPy 1.6.1 record; the root dependency file has not changed. In an environment already providing the extension dependencies, run from `extensions/`:

```sh
python code/verify_extensions.py --output-dir regenerated
python code/compare_data.py data regenerated
python code/check_integrity.py
```

The comparator checks all six JSON files and ignores only the `environment` field in `summary.json`. It does not omit mathematical fields. The source constructs the original Dyck moments and Toeplitz minors before checking the proposed leading formulas.

The included historical records cover 1,024 expanded minors in 11 variables, 884,566 terms in total, 195 generic partitions, 65,535 combinatorial-map tests through dimension 16, 24,485 lattice points, and 128 complete small minors. The dimension-16 check is a formula-bijection check, not a dimension-16 symbolic determinant calculation. The all-dimensional conclusions come from the proof.

Neither full suite was rerun for this edition. A recorded second regeneration completed in separate stages after a timeout; the original process logs and second output directory are not included. Stored counts, matching data, and hashes do not independently establish that execution history. Do not interpret these records as two uninterrupted successful runs. The default extension suite may need several minutes and hundreds of MB for expanded polynomial objects; a reduced run is not a reproduction of the default records.

The six expected files are `symbolic_minors.json`, `small_minors_full.json`, `generic_schur.json`, `bijections.json`, `hilbert_checks.json`, and `summary.json`. Sparse polynomial terms are `[exponent_vector, integer_coefficient]`, with the full ambient exponent length retained. Canonical hashes sort nonzero terms in decreasing lexicographic order and concatenate ASCII lines `e1,e2,...,en:coefficient\n`, without spaces. In particular, the 11-variable hashes retain more trailing zeros than the 8-variable complete coefficient records.

The baseline and extension dependency records and data are kept separately. No original input archive or external source PDF is required to run the extension verifier.

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
| extensions/LectureHall_extensions.tex and .pdf | Complete extension proof, including its self-contained Appendix A |
| extensions/code/ | Mathematical verifier, exact-data comparator, and manifest checker |
| extensions/data/ | Six stored exact-data files with the scope and execution limits above |
| extensions/requirements.txt | Separate extension dependency pin |
| extensions/MANIFEST.json | Extension file sizes and SHA256 hashes, excluding itself |

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

The extension is also standalone: from `extensions/`, compile `LectureHall_extensions.tex` twice using existing LaTeX dependencies. The prebuilt extension PDF is provided. On MiKTeX, the preparation build used `-disable-installer -disable-write18 -dont-parse-first-line -interaction=nonstopmode -halt-on-error`; automatic package installation and shell escape were disabled.

## References and attribution

The three primary references are Katthan2018, Sokal2023, and Flajolet1980, listed in REFERENCES.md. In particular, Sokal's Theorem 9.1(b) gives the Dyck-path interpretation and Theorem 9.5(b,c) gives the two Hankel factorizations used here. The application to Katthän's particular sequence requires the explicit signed specialization and the defining-equation check supplied in the manuscript.

## AI assistance

This work was completed with AI assistance.

