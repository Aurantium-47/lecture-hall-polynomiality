# References

The root manuscript is the corrected polynomiality baseline, [v0.1.1](https://github.com/Aurantium-47/lecture-hall-polynomiality/releases/tag/v0.1.1), commit `f6e01a2697549781bf15facf86c6f17184facfaf`. The extension in `extensions/` retains that identification as prior work and reproduces its needed foundation in Appendix A. Its new statements concern the generic leading-term formula, the specified subset map, the initial algebra, and the integral family; the baseline composition formula remains in the root manuscript.

For the extension's source problem, Katthän's Definition 4.1 fixes the minors; Conjecture 4.2(i)(ii) asks for the initial-algebra and Hilbert-basis assertions; Problem 5.1 asks for the specific leading-term subset map. The source's Theorem 4.6 already reports finite verification through `n=12`; the extension's recorded `n=11` symbolic checks are not a new finite range. The generic determinant and counting arguments in the extension are supplied in full. The classical Lecture Hall series, continued fractions, Hankel identities, and general idea of SAGBI degeneration are not presented as new concepts.

## Katthan2018

Lukas Katthän. *The Lecture Hall Cone as a toric deformation*. arXiv:1809.01377v1, 2018.

- [Version record](https://arxiv.org/abs/1809.01377)
- [Version 1 PDF](https://arxiv.org/pdf/1809.01377v1)

**Role.** Definition 3.1 specifies the Lecture Hall sequence, and Conjecture 3.4 asks whether all its terms are polynomials. The definition is interpreted using the mutually supporting square-block description on page 3, Example 3.2, and Definition 4.1. The corrected fourth term is confirmed by Section 6 and Example 4.5. Conjecture 4.2 concerns additional SAGBI and initial-algebra assertions.

## Sokal2023

Alan D. Sokal. *A simple algorithm for expanding a power series as a continued fraction*. Expositiones Mathematicae **41** (2023), 245–287. DOI: 10.1016/j.exmath.2022.12.001. arXiv:2206.15434.

- [Journal article](https://doi.org/10.1016/j.exmath.2022.12.001)
- [arXiv record](https://arxiv.org/abs/2206.15434)
- [Publisher PDF preserved by UCL](https://discovery.ucl.ac.uk/10162488/1/1-s2.0-S0723086922000792-main.pdf)

**Role.** Equation (9.3) defines the Stieltjes–Rogers polynomials. Theorem 9.1(b) identifies them as Dyck-path weight sums. Theorem 9.5(b,c) gives factorizations of their unshifted and once-shifted Hankel matrices; taking principal determinants yields the two product formulas used in the proof. Since these are polynomial identities in independent weights, they remain valid after the signed substitution in this manuscript. This is a general result, not a statement in that article identifying Katthän's sequence.

## Flajolet1980

Philippe Flajolet. *Combinatorial aspects of continued fractions*. Discrete Mathematics **32** (1980), 125–161.

- [Author's institutional PDF](https://algo.inria.fr/flajolet/Publications/Flajolet80b.pdf)

**Role.** Theorem 1, on original journal page 129, provides the general correspondence between weighted paths and formal continued fractions. It supplies the classical combinatorial framework for the Stieltjes–Rogers interpretation. The specific signed weights and the identification with the Lecture Hall sequence are established in the present manuscript.

