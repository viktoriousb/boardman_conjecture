# Formalization of a proof of Boardman's conjecture

A Lean 4 formalization of a proof of Boardman's conjecture: 

*The rings of operations of the spectra* $\mathbf{MU}$ *and* $\mathbf{BP}$ *admit no antiautomorphism of rings which preserves their coefficient ring.* 

The conjecture was originally stated in J. M. Boardman, *The eightfold way to BP-operations or* $E_*E$ *and all that*, CMS Conf. Proc. 2 (1982), p. 204.

Based on [$`\mathbf{MU}^*\mathbf{MU}`$ and $`\mathbf{BP}^*\mathbf{BP}`$ do not admit coefficient preserving antiautomorphisms of rings](https://websites.umich.edu/~viktorb/preprints/antiautomorphisms_of_mu*mu_and_bp*bp.pdf). The final remark of that paper, on the motivic analogue, is not formalized.

## Building

Requires [elan](https://github.com/leanprover/elan); the Lean and Mathlib versions are pinned in
`lean-toolchain` and `lakefile.toml`.

```bash
lake exe cache get   # download prebuilt Mathlib
lake build
```

## Type-checking online

* [Type-check it in the Lean web editor](https://live.lean-lang.org/#project=mathlib-stable&url=https%3A%2F%2Fraw.githubusercontent.com%2Fviktoriousb%2Fboardman_conjecture%2Frefs%2Fheads%2Fmain%2FBoardmanConjecture.lean)

  WARNING: The editor's Mathlib may be newer than the version pinned here, so if a
  name has changed upstream the online check can fail while the pinned build still passes. The
  pinned build (`lake build`, or the CI run) is the authoritative check, which you can reproduce in the browser via GitHub Codespaces below.
* [Type-check in GitHub Codespaces](https://codespaces.new/viktoriousb/boardman_conjecture)
