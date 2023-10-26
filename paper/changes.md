## Changes between submitted and revised version

Thanks again to the reviewers for their detailed suggestions and comments.

The revised version is now 27 pages, not including acknowledgments and bibliography.

Mandatory changes made:

1. The mistake in Atkey 2018 has been explicitly acknowledged and explained, and the relationship between the Indexed Linear Pre-order construction presented here and LCA realisability construction has been clarified. The main text for this is at the start of Section 5.2 "Models of Quantitative Type Theory from Indexed Preorders".

   Additionally, a mistake in the construction of $\mathbb{N}$-graded exponentials that was discovered when preparing the artefact has been corrected. This is the definition of $!_n$ on page 22 (for some reason latexdiff highlights the old one in red, but the new one is black not blue).

2. The equational theory of QTT(Cons-free | LFPL) has been clarified in the main text:

   1. The conversion rule, which was missing before, is given at the end of Section 3.1.2, with a short discussion of definitional equality in QTT.
   2. For description of each type, the definitional equality rules are briefly discussed. The are changes in Sections 3.1.3 ($\Pi$- and $\Sigma$-types), 3.1.5 (Universe type), 3.2.1 (Booleans), 3.2.2 (Lists), 3.3 (Cons-free naturals), 3.4 (LFPL naturals), and 3.5 (Reflection).

   The complete typing rules for the system will be made available in an online extended version on ArXiv, currently referred to as "Atkey 2023" in the main paper. The whole appendix in 7 pages long, so it goes way over the allowed POPL page limit. The extended version is attached to this comment.

3. The characterisation of polytime in terms of open programs of type $\mathbb{N} \to A$ is clarified in the introduction to Section 2, and it is made clear how this applies to the Cons-free and LFPL systems presented.

Additional changes:

1. A mistake in the naming of complexity classes was fixed. The complexity class characterised in Section 4.3.2 is BPP (Bounded-error Probabilistic Polynomial Time), not PP (Probabilistic Polynomial Time) as previously stated. This has been fixed, and all references to PP changed to BPP. BPP is the one that you actually want to characterise. References to other work by Dal Lago and others on probabilistic complexity classes has also been added, highlighting the utility of mixing dependent types and implicit computational complexity for capturing semantic complexity classes like BPP.

2. The fact that proofs of membership of PTIME (and the other classes) are carried out in the $\sigma = 0$ fragment has been made explicit (Section 4.2).

3. The iterators $I_k$ have been fixed to do exactly $n \choose k$ iterations, by removing the application of $f$ in the $I_{k+1}$ iterator. Review D pointed out that the number originally given was likely wrong, but I think their count was wrong as well. The number of iterations carried out is computed by this Haskell function

   ```haskell
   iter :: Integer -> Integer -> Integer
   iter 0 _ = 1                 -- base level, do one application of 'f'
   iter k 0 = 0                 -- end of this iteration level
   iter k n = iter (k-1) (n-1)  -- call to iterator one level down
               + iter k (n-1)   -- plus call to same level for rest of n
   ```

   A bit of testing is enough to establish that `iter k n` computes $n \choose k$.

4. Some small bits of text were added to the related and future work. Most notable is a prediction that almost all other P-time based complexity classes are likely characterisable in the system.

5. Spelling and grammatical fixes throughout, including the culling of many, spare, commas.

Changes not made, but discussed in the response:

1. No additional examples of programming in LFPL-style were added. There is not enough space for a thorough presentation of how to program in LFPL, and it has already been covered in multiple publications by Martin Hofmann.

2. I did not change the presentation of Resource Monoids to take the enriched category definition as primary, even though this is the definition used in the formal proofs. I felt that the monoid definition would be more familiar to readers, and in the absence of a presentation of the details of the proofs it is harder to motivate the $\mathbb{N}$-enriched category version.

3. Except for a little bit of text discussing BPP and other P-based classes, there is no wider discussion of the history of ICC and why it isn't more popular, as prompted by Review D. I felt that this would have been too speculative for the paper.
