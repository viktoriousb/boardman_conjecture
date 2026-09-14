import Mathlib

/-!
# Boardman's conjecture on antiautomorphisms of `E^*E`

Formalizes the note proving Boardman's conjecture [Bo, Conjecture]: for `E = MU` or `E = BP`,
the ring `E^*E` admits no antiautomorphism of rings preserving `E^*`.

Mathlib has no complex cobordism or Brown–Peterson spectra, so the topological input is
isolated into hypotheses of a purely algebraic theorem (`not_exists_isRingAntiAut`). The
dictionary with the note is as follows (case `E = MU`; `BP` is analogous with `x₁, b₁, 2`
replaced by `v₁, t₁, p` and `ℤ` by `ℤ₍ₚ₎`). The primary source for all of the `MU`/`BP` input is
Boardman's paper [Bo], which states the Conjecture on p. 204; every statement number below was
checked against [Bo] listed in the references. Where a fact is also readily found
in [Ad] or [Ra], a cross-reference is added.

* `A = MU_* = π`, `Γ = MU^*MU`, `S = ℤ`. Writing `A' = MU_*MU` for Boardman's `A`, one has
  `A' = π[b₁, b₂, …]` as a ring and left `π`-module, `b₀ = 1` ([Bo, Def. 8.1, Thm. 8.2];
  cf. [Ad, Part II, §11], [Ra, Thm. 4.1.11]); in particular `A'` is a free right `π`-module.
* `Γ ≅ D^gr_{MU_*}(MU_*MU)`: the dual `A'^* = Hom_π(A', π)` of [Bo, Def. 3.2] is a ring with
  unit `ε^* : π → A'^*` and identity element the counit `ε` [Bo, Lemma 3.4(a) and the Remark
  following it], and the universal coefficient isomorphism `MU^*MU ≅ A'^*` [Bo, Thm. 4.2,
  Thm. 5.4] is an isomorphism of rings and bimodules [Bo, Lemma 6.1] (cf. [Ad, Part III,
  Prop. 13.4–13.5], [Ra, (4.1.14)]). Under it, `ι = ε^* : π → A'^*` is Boardman's copy of `π`
  in `E^*E` (the subring of actions `W(k)`, [Bo, p. 202]).
* `ev : Γ → A` is evaluation at `1 ∈ A'`. Left `π`-linearity of `ev` is the bimodule structure
  of [Bo, Lemma 3.4(a)] ("multiplication with `ε^*` on either side"), and `ev 1 = ε(1) = 1`
  since `ε = μ_* : A' → π` is a ring homomorphism [Bo, Lemma 5.6, Thm. 5.2].
* `aug : MU_* → ℤ` is the augmentation `x₁ ↦ 0` of the polynomial ring `MU_* ≅ ℤ[x₁, x₂, …]`,
  `x = x₁`, `aug x₁ = 0`.
* `B n = B_n` is the dual of `b₁ⁿ`, so `B 0 = ε = 1`, and `B_n x₁ = x₁ B_n + 2 B_{n-1}`
  (equation (1) of the note). The note derives this from `η_R(x₁) = x₁ + 2 b₁`, which follows
  from [Bo, (8.6)]: `b(F_L(x, y)) = F_R(b(x), b(y))` with `b(z) = ∑ᵢ bᵢ z^{i+1}`; comparing the
  coefficients of `xy` gives `η_R(a₁₁) = a₁₁ + 2 b₁`, and `x₁ = a₁₁ = -2m₁` generates `π₂`
  [Bo, p. 211] (cf. [Ad, Part II, Thm. 11.3(iii) with (7.5)], [Ra, Thm. 4.1.11]).
* `Y : ℤ^ℕ → MU^*MU`, `a ↦ ∑ₙ aₙ x₁ⁿ B_n`, is the summation map that exists because the sequence
  `(x₁ⁿ B_n)ₙ` is pointwise finite and concentrated in a single degree (Example `mu` and
  Remark `prop_for_graded` of the note). This is the one hypothesis with no literature source:
  it packages the note's own Remark on the graded case.

For `E = BP` ([Bo, §9]): `BP_*BP = π[t₁, t₂, …]`, `t₀ = 1` [Bo, Thm. 9.4] (cf.
[Ra, Thm. 4.1.18–4.1.19], [Ad, Part II, §16]); the duality `BP^*BP ≅ (BP_*BP)^*` is again
[Bo, Thm. 5.4, Lemma 6.1] (cf. [Ad, Part II, §16, p. 151]); with Hazewinkel generators
`vₙ = p mₙ - ∑_{j<n} mⱼ v_{n-j}^{pʲ}` [Bo, (9.1)] and Adams' `tᵢ` defined by
`log_R z = ∑ᵢ log_L tᵢ z^{pⁱ}` [Bo, (9.3)], comparing coefficients of `z^p` gives
`η_R(m₁) = m₁ + t₁`, hence `η_R(v₁) = p η_R(m₁) = v₁ + p t₁` (for `p = 2` this is `w₁ = v₁ + 2t₁`
in [Bo, (9.7)]; cf. [Ra, (A2.2.1), Thm. 4.1.18(iv)]), as used in Example `bp` of the note.

The other statements of the note (Definition of antiautomorphism, pointwise finite sequences,
Remarks 1–2, the Proposition) are formalized faithfully. Throughout, the ring `A` of the note is
taken to be commutative (as it is in every application: `MU_*`, `BP_*`). The final Remark of
the note (the motivic spectra `MGL` and `BP` over a base field) is not formalized here; see the
comment at the end of the file.

## Slender abelian groups

The first part of the file (up to `Slender.prod`) is the theory of slender groups used in the
proof. Formalizes the notion of a *slender* abelian group (Definition `slender` of the note on
Boardman's conjecture, following Fuchs, *Abelian Groups*, §13.2) together with the examples
used there:

* `ℤ` is slender (Specker's theorem),
* the `(p)`-local integers `ℤ₍ₚ₎` are slender,
* (finite) direct sums of slender groups are slender.

An abelian group `S` is slender if, for every abelian group `M`, the natural map
`Hom(M^ℕ, S) → ⊕_ℕ Hom(M, S)`, `f ↦ (f ∘ ι_n)_n` is a bijection, where `ι_n : M → M^ℕ` is the
`n`-th coordinate inclusion. We also record Fuchs' definition (`WeakSlender`, [Fu, Ch. 13, §2]):
every homomorphism `ℤ^ℕ → S` vanishes on almost all unit vectors `e_n`, and prove the two
notions equivalent (`slender_iff_weakSlender`).

The note cites [Fu, 13.2.5] for its three examples; that is Example 2.5 of Chapter 13 of [Fu]
("`ℤ`, every proper subgroup of `ℚ`, and direct sums of these are slender"), which rests on
Lemma 2.3 (Sąsiada: a torsion-free group of cardinality less than the continuum is slender iff
it is reduced) and Lemma 2.4 (direct sums of slender groups are slender). Rather than cite
these, we prove what is needed: `weakSlender_of_countable` is a self-contained variant of
Sąsiada's argument for countable groups (with reducedness only demanded along powers of one
integer `q`), specialised to `ℤ` (Specker's theorem [Sp]) and to `ℤ₍ₚ₎`; `Slender.prod` covers
finite direct sums only.

## References

* [Bo] J. M. Boardman, *The eightfold way to BP-operations or E_*E and all that*, Current trends
  in algebraic topology, Part 1 (London, Ont., 1981), CMS Conf. Proc. 2, AMS, 1982, 187–226.
  Primary source for the `MU`/`BP` input; checked against the scan at
  https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/boardman-8.pdf.
* [Ad] J. F. Adams, *Stable Homotopy and Generalised Homology*, Chicago Lectures in Math., 1974.
* [Ra] D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, 2nd ed.,
  AMS Chelsea, 2004.
* [Fu] L. Fuchs, *Abelian Groups*, Springer Monographs in Mathematics, 2015 (Chapter 13, §2).
* [Sp] E. Specker, *Additive Gruppen von Folgen ganzer Zahlen*, Portugaliae Math. 9 (1950),
  131–140.
-/

namespace BoardmanConjecture

open Function

universe u v

/-! ### Slender abelian groups -/

section Definitions

variable (S : Type v) [AddCommGroup S]

/-- **Definition (slender).** `S` is slender if for every abelian group `M` the natural map
`Hom(M^ℕ, S) → ⊕_ℕ Hom(M, S)`, `f ↦ (f ∘ ι_n)_n`, is a bijection; i.e. there is a bijection
`Hom(M^ℕ, S) ≃ (ℕ →₀ Hom(M, S))` whose `n`-th component is precomposition with the coordinate
inclusion `ι_n = AddMonoidHom.single _ n`. -/
def Slender : Prop :=
  ∀ (M : Type u) [AddCommGroup M],
    ∃ e : ((ℕ → M) →+ S) ≃ (ℕ →₀ (M →+ S)),
      ∀ (f : (ℕ → M) →+ S) (n : ℕ), e f n = f.comp (AddMonoidHom.single (fun _ => M) n)

/-- Fuchs' formulation of slenderness: every homomorphism `ℤ^ℕ → S` vanishes on all but
finitely many of the unit vectors `e_n = Pi.single n 1`. -/
def WeakSlender : Prop :=
  ∀ f : (ℕ → ℤ) →+ S, {n : ℕ | f (Pi.single n 1) ≠ 0}.Finite

end Definitions

section Equivalence

variable {S : Type v} [AddCommGroup S]

/-- For a slender group, every homomorphism `M^ℕ → S` vanishes on almost all coordinate
inclusions. -/
theorem Slender.finite_support (hS : Slender.{u} S) {M : Type u} [AddCommGroup M]
    (f : (ℕ → M) →+ S) : {n : ℕ | f.comp (AddMonoidHom.single (fun _ => M) n) ≠ 0}.Finite := by
  obtain ⟨e, he⟩ := hS M
  refine (e f).hasFiniteSupport.subset ?_
  intro n hn
  rw [Function.mem_support, he]
  exact hn

/-- Slender groups are weakly slender. -/
theorem Slender.weakSlender (hS : Slender.{0} S) : WeakSlender S := by
  intro f
  refine (hS.finite_support f).subset ?_
  intro n hn h
  apply hn
  simpa using DFunLike.congr_fun h 1

/-- Weakly slender groups: every homomorphism `M^ℕ → S` vanishes on almost all coordinate
inclusions, for every abelian group `M`. -/
theorem WeakSlender.finite_support (hS : WeakSlender S) {M : Type u} [AddCommGroup M]
    (f : (ℕ → M) →+ S) : {n : ℕ | f.comp (AddMonoidHom.single (fun _ => M) n) ≠ 0}.Finite := by
  -- choose, for each `n` with `f ∘ ι_n ≠ 0`, an element `mm n` with `f (ι_n (mm n)) ≠ 0`
  have hex : ∀ n, ∃ m : M,
      f.comp (AddMonoidHom.single (fun _ => M) n) ≠ 0 → f (Pi.single n m) ≠ 0 := by
    intro n
    by_cases h : f.comp (AddMonoidHom.single (fun _ => M) n) = 0
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨m, hm⟩ := DFunLike.ne_iff.mp h
      exact ⟨m, fun _ => by simpa using hm⟩
  choose mm hmm using hex
  -- the homomorphism `ℤ^ℕ → M^ℕ`, `b ↦ (bₙ • mm n)ₙ`
  let φ : (ℕ → ℤ) →+ (ℕ → M) :=
    { toFun := fun b i => b i • mm i
      map_zero' := by
        ext i
        simp
      map_add' := fun b b' => by
        ext i
        simp [add_smul] }
  have hφ : ∀ n, φ (Pi.single n 1) = Pi.single n (mm n) := by
    intro n
    ext i
    by_cases h : i = n
    · subst h
      simp [φ]
    · simp [φ, Pi.single_eq_of_ne h]
  refine (hS (f.comp φ)).subset ?_
  intro n hn
  simp only [Set.mem_ofPred_eq, AddMonoidHom.comp_apply, hφ]
  exact hmm n hn

/-- Weakly slender groups: a homomorphism `M^ℕ → S` is determined by its restrictions to the
coordinate inclusions. -/
theorem WeakSlender.ext (hS : WeakSlender S) {M : Type u} [AddCommGroup M]
    {f g : (ℕ → M) →+ S}
    (h : ∀ n, f.comp (AddMonoidHom.single (fun _ => M) n) =
      g.comp (AddMonoidHom.single (fun _ => M) n)) : f = g := by
  -- it suffices to treat `h = f - g`, which vanishes on all coordinate inclusions
  suffices key : ∀ h : (ℕ → M) →+ S,
      (∀ n, h.comp (AddMonoidHom.single (fun _ => M) n) = 0) → h = 0 by
    rw [← sub_eq_zero]
    exact key (f - g) fun n => by rw [AddMonoidHom.sub_comp, h n, sub_self]
  intro h hh
  ext a
  by_contra ha
  -- the homomorphism `ℤ^ℕ → M^ℕ`, `b ↦ ((b₀ + ⋯ + bᵢ) • aᵢ)ᵢ`; it sends `eₙ` to the tail of `a`
  let ψ : (ℕ → ℤ) →+ (ℕ → M) :=
    { toFun := fun b i => (∑ j ∈ Finset.range (i + 1), b j) • a i
      map_zero' := by
        ext i
        simp
      map_add' := fun b b' => by
        ext i
        simp [Finset.sum_add_distrib, add_smul] }
  have hψ : ∀ n, ψ (Pi.single n 1) = fun i => if n ≤ i then a i else 0 := by
    intro n
    ext i
    simp only [ψ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finset.sum_pi_single', Finset.mem_range]
    by_cases hni : n ≤ i
    · rw [if_pos hni, if_pos (by omega), one_smul]
    · rw [if_neg hni, if_neg (by omega), zero_smul]
  have hsplit : ∀ n, a = (∑ j ∈ Finset.range n, Pi.single j (a j)) + ψ (Pi.single n 1) := by
    intro n
    ext i
    simp only [Pi.add_apply, Finset.sum_apply, Finset.sum_pi_single, Finset.mem_range, hψ]
    by_cases hni : n ≤ i
    · rw [if_neg (by omega), if_pos hni, zero_add]
    · rw [if_pos (by omega), if_neg hni, add_zero]
  have hzero : ∀ j, h (Pi.single j (a j)) = 0 := fun j => by
    simpa using DFunLike.congr_fun (hh j) (a j)
  have hval : ∀ n, (h.comp ψ) (Pi.single n 1) = h a := by
    intro n
    have := congrArg h (hsplit n)
    rw [map_add, map_sum, Finset.sum_eq_zero (fun j _ => hzero j), zero_add] at this
    exact this.symm
  have huniv : {n : ℕ | (h.comp ψ) (Pi.single n 1) ≠ 0} = Set.univ :=
    Set.eq_univ_of_forall fun n => by
      rw [Set.mem_ofPred_eq, hval]
      exact ha
  have := hS (h.comp ψ)
  rw [huniv] at this
  exact Set.infinite_univ this

/-- Weakly slender groups are slender. -/
theorem WeakSlender.slender (hS : WeakSlender S) : Slender.{u} S := by
  intro M _
  -- the inverse map `⊕_ℕ Hom(M, S) → Hom(M^ℕ, S)`, `(gₙ)ₙ ↦ ∑ₙ gₙ ∘ πₙ`
  let inv : (ℕ →₀ (M →+ S)) → ((ℕ → M) →+ S) :=
    fun g => g.sum fun n φ => φ.comp (Pi.evalAddMonoidHom (fun _ => M) n)
  have hinv : ∀ (g : ℕ →₀ (M →+ S)) (n : ℕ),
      (inv g).comp (AddMonoidHom.single (fun _ => M) n) = g n := by
    intro g n
    ext m
    simp only [inv, Finsupp.sum, AddMonoidHom.comp_apply, AddMonoidHom.finsetSum_apply,
      AddMonoidHom.single_apply, Pi.evalAddMonoidHom_apply]
    rw [Finset.sum_eq_single n]
    · rw [Pi.single_eq_same]
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk, map_zero]
    · intro hn
      simp [Finsupp.notMem_support_iff.mp hn]
  refine ⟨{ toFun := fun f => Finsupp.ofSupportFinite
              (fun n => f.comp (AddMonoidHom.single (fun _ => M) n)) (hS.finite_support f)
            invFun := inv
            left_inv := fun f => hS.ext fun n => by rw [hinv]; rfl
            right_inv := fun g => Finsupp.ext fun n => hinv g n }, fun f n => rfl⟩

/-- The two notions of slenderness agree. -/
theorem slender_iff_weakSlender : Slender.{0} S ↔ WeakSlender S :=
  ⟨Slender.weakSlender, WeakSlender.slender⟩

end Equivalence

section Examples

variable {S : Type v} [AddCommGroup S]

open scoped Classical in
/-- Partial sums `s_K` of the diagonal sequence in the proof of the Specker-type criterion:
`s_{K+1} = s_K + c_K • g_K`, where the coefficient `c_K ∈ {0, N_K}` is chosen so that
`m_K - s_{K+1}` is *not* divisible by `N_{K+1}`. -/
noncomputable def speckerSum (N : ℕ → ℕ) (g m : ℕ → S) : ℕ → S
  | 0 => 0
  | K + 1 =>
    speckerSum N g m K +
      (if ∃ t : S, N (K + 1) • t = m K - speckerSum N g m K - N K • g K then 0 else N K • g K)

open scoped Classical in
/-- The coefficients `c_K ∈ {0, N_K}` of the diagonal sequence, see `speckerSum`. -/
noncomputable def speckerCoeff (N : ℕ → ℕ) (g m : ℕ → S) (K : ℕ) : ℤ :=
  if ∃ t : S, N (K + 1) • t = m K - speckerSum N g m K - N K • g K then 0 else N K

/-- Recursion for the partial sums: `s_{K+1} = s_K + c_K • g_K`. -/
theorem speckerSum_succ (N : ℕ → ℕ) (g m : ℕ → S) (K : ℕ) :
    speckerSum N g m (K + 1) = speckerSum N g m K + speckerCoeff N g m K • g K := by
  simp only [speckerSum, speckerCoeff]
  split_ifs <;> simp [natCast_zsmul]

/-- The partial sums are `s_K = ∑_{j < K} c_j • g_j`. -/
theorem speckerSum_eq_sum (N : ℕ → ℕ) (g m : ℕ → S) (K : ℕ) :
    speckerSum N g m K = ∑ j ∈ Finset.range K, speckerCoeff N g m j • g j := by
  induction K with
  | zero => simp [speckerSum]
  | succ K ih => rw [speckerSum_succ, Finset.sum_range_succ, ih]

/-- The coefficient `c_K` is divisible by the modulus `N_K`. -/
theorem natCast_dvd_speckerCoeff (N : ℕ → ℕ) (g m : ℕ → S) (K : ℕ) :
    (N K : ℤ) ∣ speckerCoeff N g m K := by
  unfold speckerCoeff
  split_ifs <;> simp

/-- **Specker-type criterion.** A countable abelian group `S` which has no `q`-torsion and is
`q`-reduced (no nonzero element is divisible by every power of `q`) is weakly slender. -/
theorem weakSlender_of_countable [Countable S] (q : ℕ)
    (htf : ∀ s : S, q • s = 0 → s = 0)
    (hred : ∀ s : S, s ≠ 0 → ∃ e : ℕ, ∀ t : S, q ^ e • t ≠ s) : WeakSlender S := by
  intro f
  by_contra hinf
  -- enumerate the infinitely many `n` with `f eₙ ≠ 0` increasingly as `ν 0 < ν 1 < ⋯`
  have hI : (Set.ofPred fun n => f (Pi.single n 1) ≠ 0).Infinite := hinf
  let ν : ℕ → ℕ := Nat.nth fun n => f (Pi.single n 1) ≠ 0
  have hν : StrictMono ν := Nat.nth_strictMono hI
  let g : ℕ → S := fun k => f (Pi.single (ν k) 1)
  have hg : ∀ k, g k ≠ 0 := fun k => Nat.nth_mem_of_infinite hI k
  -- exponents `e k` with `g k ∉ q ^ e k • S`
  choose e he using fun k => hred (g k) (hg k)
  -- the moduli `N K = ∏_{j < K} q ^ e j`
  let N : ℕ → ℕ := fun K => ∏ j ∈ Finset.range K, q ^ e j
  have hN0 : N 0 = 1 := by simp [N]
  have hNsucc : ∀ K, N (K + 1) = N K * q ^ e K := fun K => Finset.prod_range_succ _ _
  have hNdvd : ∀ {K k : ℕ}, K ≤ k → N K ∣ N k := fun {K k} hKk =>
    Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_mono hKk)
  have hqtf : ∀ (j : ℕ) (s : S), q ^ j • s = 0 → s = 0 := by
    intro j
    induction j with
    | zero => intro s hs; simpa using hs
    | succ j ih => intro s hs; rw [pow_succ, mul_comm, mul_smul] at hs; exact ih _ (htf _ hs)
  have hNtf : ∀ (K : ℕ) (s : S), N K • s = 0 → s = 0 := by
    intro K
    induction K with
    | zero => intro s hs; simpa [hN0] using hs
    | succ K ih => intro s hs; rw [hNsucc, mul_smul] at hs; exact hqtf _ _ (ih _ hs)
  -- enumerate `S`
  obtain ⟨m, hm⟩ := exists_surjective_nat S
  -- the diagonal element `a = ∑ₖ c k • e_{ν k} ∈ ℤ^ℕ`
  let c : ℕ → ℤ := speckerCoeff N g m
  have hcdvd : ∀ {K k : ℕ}, K ≤ k → (N K : ℤ) ∣ c k := fun {K k} hKk =>
    (Int.natCast_dvd_natCast.mpr (hNdvd hKk)).trans (natCast_dvd_speckerCoeff N g m k)
  let a : ℕ → ℤ := Function.extend ν c 0
  have ha : ∀ k, a (ν k) = c k := fun k => hν.injective.extend_apply _ _ _
  have ha' : ∀ i, (¬ ∃ k, ν k = i) → a i = 0 := fun i hi => Function.extend_apply' _ _ _ hi
  -- the remainders `r K`, with `a = ∑_{j < K} c j • e_{ν j} + N K • r K`
  let r : ℕ → ℕ → ℤ := fun K => Function.extend ν (fun k => if K ≤ k then c k / N K else 0) 0
  have hr : ∀ K k, r K (ν k) = if K ≤ k then c k / N K else 0 :=
    fun K k => hν.injective.extend_apply _ _ _
  have hr' : ∀ K i, (¬ ∃ k, ν k = i) → r K i = 0 := fun K i hi => Function.extend_apply' _ _ _ hi
  have hsplit : ∀ K, a = (∑ j ∈ Finset.range K, Pi.single (ν j) (c j)) + (N K : ℤ) • r K := by
    intro K
    ext i
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hi : ∃ k, ν k = i
    · obtain ⟨k, rfl⟩ := hi
      rw [ha, hr]
      by_cases hk : k < K
      · rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr hk)
          (fun j _ hj => Pi.single_eq_of_ne (fun h => hj (hν.injective h).symm) _),
          Pi.single_eq_same, if_neg (by omega), mul_zero, add_zero]
      · rw [Finset.sum_eq_zero (fun j hj => Pi.single_eq_of_ne
          (fun h => by have := hν.injective h; rw [Finset.mem_range] at hj; omega) _),
          if_pos (by omega), zero_add, Int.mul_ediv_cancel' (hcdvd (by omega))]
    · rw [ha' i hi, hr' K i hi, mul_zero, add_zero]
      exact (Finset.sum_eq_zero fun j _ =>
        Pi.single_eq_of_ne (fun h => hi ⟨j, h.symm⟩) _).symm
  have hfa : ∀ K, f a = speckerSum N g m K + N K • f (r K) := by
    intro K
    rw [speckerSum_eq_sum]
    conv_lhs => rw [hsplit K]
    rw [map_add, map_sum, map_zsmul, natCast_zsmul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : (Pi.single (ν j) (c j) : ℕ → ℤ) = c j • Pi.single (ν j) (1 : ℤ) := by
      rw [← Pi.single_smul', smul_eq_mul, mul_one]
    rw [h1, map_zsmul]
  -- `f a = m K` for some `K`; the choice of `c K` rules this out
  obtain ⟨K, hK⟩ := hm (f a)
  have hstep := hfa (K + 1)
  rw [speckerSum_succ, hNsucc, mul_smul] at hstep
  by_cases hP : ∃ t : S, N (K + 1) • t = m K - speckerSum N g m K - N K • g K
  · obtain ⟨t, ht⟩ := hP
    have hc : speckerCoeff N g m K = 0 := by
      unfold speckerCoeff
      rw [if_pos ⟨t, ht⟩]
    rw [hc, zero_smul, add_zero] at hstep
    rw [hNsucc, mul_smul] at ht
    -- `N K • g K = N K • (q ^ e K • (f (r (K+1)) - t))`
    have h1 : N K • (q ^ e K • (f (r (K + 1)) - t) - g K) = 0 := by
      rw [smul_sub, smul_sub, smul_sub, ht, hK, hstep]
      abel
    exact he K _ (sub_eq_zero.mp (hNtf K _ h1))
  · have hc : speckerCoeff N g m K = N K := by
      unfold speckerCoeff
      rw [if_neg hP]
    rw [hc, natCast_zsmul] at hstep
    apply hP
    refine ⟨f (r (K + 1)), ?_⟩
    rw [hNsucc, mul_smul, hK, hstep]
    abel

/-- **Example.** The integers `ℤ` form a slender group (Specker [Sp]; [Fu, Ch. 13, Ex. 2.5]). -/
theorem slender_int : Slender.{u} ℤ := by
  refine WeakSlender.slender (weakSlender_of_countable 2 (fun s h => by simpa using h) ?_)
  intro s hs
  refine ⟨s.natAbs, fun t ht => hs ?_⟩
  rw [nsmul_eq_mul] at ht
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (Dvd.intro t ht) ?_
  rw [Int.natAbs_natCast]
  exact Nat.lt_two_pow_self

/-- The ideal `(p) ⊆ ℤ` is prime for a prime `p`. -/
instance instIsPrime_span_natPrime (p : ℕ) [hp : Fact p.Prime] : (Ideal.span {(p : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).2
    (Nat.prime_iff_prime_int.mp hp.out)

/-- The `(p)`-local integers `ℤ₍ₚ₎`, i.e. the localization of `ℤ` at the prime ideal `(p)`. -/
abbrev IntLocalAtPrime (p : ℕ) [Fact p.Prime] : Type := Localization.AtPrime (Ideal.span {(p : ℤ)})

instance (p : ℕ) [Fact p.Prime] : CharZero (IntLocalAtPrime p) :=
  charZero_of_injective_algebraMap
    (IsLocalization.injective (IntLocalAtPrime p)
      (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {(p : ℤ)})))

instance (p : ℕ) [Fact p.Prime] : Countable (IntLocalAtPrime p) :=
  (IsLocalization.mk'_surjective (Ideal.span {(p : ℤ)}).primeCompl
    (S := IntLocalAtPrime p)).countable

/-- **Example.** The `(p)`-local integers `ℤ₍ₚ₎` form a slender group
([Fu, Ch. 13, Ex. 2.5]: proper subgroups of `ℚ` are slender). -/
theorem slender_intLocalAtPrime (p : ℕ) [hp : Fact p.Prime] :
    Slender.{u} (IntLocalAtPrime p) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hp0 : ((p : ℤ) : IntLocalAtPrime p) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero (R := IntLocalAtPrime p)).mpr hp.out.ne_zero
  refine WeakSlender.slender (weakSlender_of_countable p ?_ ?_)
  · intro s hs
    rw [nsmul_eq_mul, mul_eq_zero] at hs
    exact hs.resolve_left (by exact_mod_cast hp0)
  · intro s hs
    obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (Ideal.span {(p : ℤ)}).primeCompl
      (S := IntLocalAtPrime p) s
    refine ⟨a.natAbs, fun t ht => hs ?_⟩
    obtain ⟨⟨a', b'⟩, rfl⟩ := IsLocalization.mk'_surjective (Ideal.span {(p : ℤ)}).primeCompl
      (S := IntLocalAtPrime p) t
    simp only at ht ⊢
    rw [nsmul_eq_mul, ← map_natCast (algebraMap ℤ (IntLocalAtPrime p)),
      IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq] at ht
    have hinj := IsLocalization.injective (IntLocalAtPrime p)
      (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {(p : ℤ)}))
    have heq := hinj ht
    push_cast at heq
    have hb' : ¬ (p : ℤ) ∣ (b' : ℤ) := fun h => b'.2 (Ideal.mem_span_singleton.mpr h)
    have hdvd : (p : ℤ) ^ a.natAbs ∣ (b' : ℤ) * a := ⟨(b : ℤ) * a', by rw [← heq]; ring⟩
    have ha : a = 0 := by
      refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
        (Prime.pow_dvd_of_dvd_mul_left hp' _ hb' hdvd) ?_
      rw [Int.natAbs_pow, Int.natAbs_natCast]
      exact Nat.lt_pow_self hp.out.one_lt
    rw [ha, IsLocalization.mk'_zero]

/-- **Example.** The direct sum of two slender groups is slender (hence so is any finite direct
sum). The general statement for arbitrary direct sums is [Fu, Ch. 13, Lemma 2.4] and is not
formalized here. -/
theorem Slender.prod {T : Type v} [AddCommGroup T] (hS : Slender.{0} S) (hT : Slender.{0} T) :
    Slender.{u} (S × T) := by
  refine WeakSlender.slender fun f => ?_
  refine ((hS.weakSlender ((AddMonoidHom.fst S T).comp f)).union
    (hT.weakSlender ((AddMonoidHom.snd S T).comp f))).subset ?_
  intro n hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, AddMonoidHom.comp_apply, AddMonoidHom.coe_fst,
    AddMonoidHom.coe_snd] at hn ⊢
  by_contra h
  obtain ⟨h1, h2⟩ := not_or.mp h
  exact hn (Prod.ext (not_not.mp h1) (not_not.mp h2))

end Examples

/-! ### Antiautomorphisms of rings -/

/-- **Definition (antiautomorphism).** A bijection `σ : R → R` preserving `1` and sums and
reversing products. -/
structure IsRingAntiAut {R : Type*} [Ring R] (σ : R → R) : Prop where
  bijective : Function.Bijective σ
  map_one : σ 1 = 1
  map_add : ∀ a b, σ (a + b) = σ a + σ b
  map_mul_rev : ∀ a b, σ (a * b) = σ b * σ a

/-- An antiautomorphism of `R` is the same thing as a ring isomorphism `R ≃+* Rᵐᵒᵖ`. -/
theorem isRingAntiAut_iff_exists_ringEquiv_mulOpposite {R : Type*} [Ring R] (σ : R → R) :
    IsRingAntiAut σ ↔ ∃ e : R ≃+* Rᵐᵒᵖ, ∀ r, e r = MulOpposite.op (σ r) := by
  constructor
  · rintro ⟨hbij, h1, hadd, hmul⟩
    have h0 : σ 0 = 0 := by
      have h := hadd 0 0
      rw [add_zero] at h
      exact (add_eq_left.mp h.symm)
    let φ : R →+* Rᵐᵒᵖ :=
      { toFun := fun r => MulOpposite.op (σ r)
        map_one' := by simp [h1]
        map_mul' := fun a b => by simp [hmul, MulOpposite.op_mul]
        map_zero' := by simp [h0]
        map_add' := fun a b => by simp [hadd] }
    exact ⟨RingEquiv.ofBijective φ (MulOpposite.op_bijective.comp hbij), fun r => rfl⟩
  · rintro ⟨e, he⟩
    have hσ : σ = fun r => MulOpposite.unop (e r) := by
      funext r
      rw [he, MulOpposite.unop_op]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hσ]
      exact MulOpposite.unop_bijective.comp e.bijective
    · apply MulOpposite.op_injective
      rw [← he, map_one, MulOpposite.op_one]
    · intro a b
      apply MulOpposite.op_injective
      rw [← he, map_add, he, he, MulOpposite.op_add]
    · intro a b
      apply MulOpposite.op_injective
      rw [← he, map_mul, he, he, MulOpposite.op_mul]

/-! ### Pointwise finite sequences -/

/-- **Definition (pointwise finite).** A sequence of maps `xₙ : M → N` is pointwise finite if
for every `m : M` only finitely many `xₙ m` are nonzero. -/
def PointwiseFinite {M N : Type*} [Zero N] (x : ℕ → M → N) : Prop :=
  ∀ m : M, {n : ℕ | x n m ≠ 0}.Finite

section PointwiseFinite

variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N]
  [Module A N]

/-- **Remark 1.** A sequence of `A`-linear maps `M → N` is pointwise finite iff evaluation
induces an `A`-linear map `M → ⊕_ℕ N`. -/
theorem pointwiseFinite_iff_exists_linearMap_finsupp (x : ℕ → M →ₗ[A] N) :
    PointwiseFinite (fun n => ⇑(x n)) ↔
      ∃ φ : M →ₗ[A] (ℕ →₀ N), ∀ m n, φ m n = x n m := by
  constructor
  · intro hx
    refine ⟨{ toFun := fun m => Finsupp.ofSupportFinite (fun n => x n m) (hx m)
              map_add' := fun m m' => by
                ext n
                show x n (m + m') = x n m + x n m'
                exact map_add _ _ _
              map_smul' := fun a m => by
                ext n
                show x n (a • m) = a • x n m
                exact map_smul _ _ _ }, fun m n => rfl⟩
  · rintro ⟨φ, hφ⟩ m
    refine (φ m).hasFiniteSupport.subset ?_
    intro n hn
    simpa [hφ] using hn

/-- **Remark 1.** The pointwise finite sequences form an `A`-submodule of `Hom_A(M, N)^ℕ`. -/
def pointwiseFiniteSubmodule (A M N : Type*) [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] : Submodule A (ℕ → M →ₗ[A] N) where
  carrier := {x | PointwiseFinite (fun n => ⇑(x n))}
  zero_mem' := by
    intro m
    simp
  add_mem' := by
    intro x y hx hy m
    refine ((hx m).union (hy m)).subset ?_
    intro n hn
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    simp [h.1, h.2] at hn
  smul_mem' := by
    intro a x hx m
    refine (hx m).subset ?_
    intro n hn
    by_contra h
    simp only [Set.mem_ofPred_eq, not_not] at h
    simp [h] at hn

/-- **Remark 2.** Pointwise finiteness only depends on the underlying additive maps. -/
theorem pointwiseFinite_toAddMonoidHom_iff (x : ℕ → M →ₗ[A] N) :
    PointwiseFinite (fun n => ⇑(x n).toAddMonoidHom) ↔ PointwiseFinite (fun n => ⇑(x n)) :=
  Iff.rfl

end PointwiseFinite

/-! ### The Proposition -/

/-- Abstract form of the **Proposition**: if `Y : ℤ^ℕ → Γ` is any homomorphism (think of
`Y a = ∑ₙ aₙ xₙ` for a pointwise finite sequence `(xₙ)`), `σ : Γ → Γ` any additive map,
`ev : Γ → N` additive (evaluation at a point) and `s : N → S` a homomorphism into a slender
group, then `s (ev (σ (Y eₙ)))` vanishes for almost all `n`. -/
theorem finite_of_weakSlender {Γ N S : Type*} [AddCommGroup Γ] [AddCommGroup N]
    [AddCommGroup S] (hS : WeakSlender S) (Y : (ℕ → ℤ) →+ Γ) (σ : Γ →+ Γ) (ev : Γ →+ N)
    (s : N →+ S) : {n : ℕ | s (ev (σ (Y (Pi.single n 1)))) ≠ 0}.Finite := by
  simpa using hS (s.comp (ev.comp (σ.comp Y)))

/-- **Proposition (main observation).** Let `(xₙ) ∈ Hom_A(M, N)^ℕ` be pointwise finite,
`σ : Hom_A(M, N) → Hom_A(M, N)` an endomorphism of abelian groups and `s : N → S` a group
homomorphism into a slender group. Then `((s_* ∘ σ)(xₙ))ₙ ∈ Hom_ℤ(M, S)^ℕ` is pointwise
finite. -/
theorem pointwiseFinite_map_of_slender {A M N S : Type*} [CommRing A] [AddCommGroup M]
    [Module A M]
    [AddCommGroup N] [Module A N] [AddCommGroup S] (hS : Slender.{0} S)
    (x : ℕ → M →ₗ[A] N) (hx : PointwiseFinite (fun n => ⇑(x n)))
    (σ : (M →ₗ[A] N) →+ (M →ₗ[A] N)) (s : N →+ S) :
    PointwiseFinite (fun n => ⇑(s.comp (σ (x n)).toAddMonoidHom)) := by
  intro m
  -- the summation map `a ↦ ∑ₙ aₙ xₙ`, well defined since `(xₙ)` is pointwise finite
  have hfin : ∀ (a : ℕ → ℤ) (m' : M), Function.HasFiniteSupport (fun n => a n • x n m') :=
    fun a m' => (hx m').subset (fun n hn => by
      simp only [Function.mem_support] at hn
      simp only [Set.mem_ofPred_eq]
      exact fun h => hn (by rw [h, smul_zero]))
  let Y : (ℕ → ℤ) →+ (M →ₗ[A] N) :=
    { toFun := fun a =>
        { toFun := fun m' => ∑ᶠ n, a n • x n m'
          map_add' := fun m₁ m₂ => by
            simp only [map_add, smul_add]
            exact finsum_add_distrib (hfin a m₁) (hfin a m₂)
          map_smul' := fun r m' => by
            simp only [map_smul, RingHom.id_apply]
            rw [smul_finsum' r (hfin a m')]
            exact finsum_congr fun n => smul_comm _ _ _ }
      map_zero' := by
        ext m'
        simp
      map_add' := fun a b => by
        ext m'
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Pi.add_apply, add_smul]
        exact finsum_add_distrib (hfin a m') (hfin b m') }
  have hY : ∀ n, Y (Pi.single n 1) = x n := by
    intro n
    ext m'
    show ∑ᶠ k, (Pi.single n (1 : ℤ) : ℕ → ℤ) k • x k m' = x n m'
    rw [finsum_eq_single _ n (fun k hk => by simp [Pi.single_eq_of_ne hk])]
    simp
  have h := finite_of_weakSlender hS.weakSlender Y σ (LinearMap.evalAddMonoidHom m) s
  simp only [hY, LinearMap.evalAddMonoidHom_apply] at h
  simpa using h

/-! ### The main theorem -/

/-- Auxiliary computation for the main theorem: if `σ` reverses products, `σ (ι x) = ι y`,
`B 0 = 1` and `B (n+1) * ι x = ι x * B (n+1) + c • B n`, then
`σ (B n) * (ι y)^n ≡ (-c)^n (mod ι y * Γ)`. -/
theorem exists_antiAut_mul_pow_eq {A Γ : Type*} [CommRing A] [Ring Γ] (ι : A →+* Γ)
    (σ : Γ →+ Γ) (hσ : ∀ a b, σ (a * b) = σ b * σ a) (hσ1 : σ 1 = 1)
    (x y : A) (hxy : σ (ι x) = ι y) (c : ℤ) (B : ℕ → Γ) (hB0 : B 0 = 1)
    (hB : ∀ n, B (n + 1) * ι x = ι x * B (n + 1) + c • B n) (n : ℕ) :
    ∃ γ : Γ, σ (B n) * ι y ^ n = ι (((-c) ^ n : ℤ) : A) + ι y * γ := by
  induction n with
  | zero =>
    exact ⟨0, by simp [hB0, hσ1]⟩
  | succ n ih =>
    obtain ⟨γ, hγ⟩ := ih
    have h := congrArg σ (hB n)
    rw [hσ, hxy, map_add, hσ, hxy, map_zsmul] at h
    have hcomm : σ (B (n + 1)) * ι y = ι y * σ (B (n + 1)) - c • σ (B n) :=
      eq_sub_of_add_eq h.symm
    refine ⟨σ (B (n + 1)) * ι y ^ n - c • γ, ?_⟩
    calc σ (B (n + 1)) * ι y ^ (n + 1)
        = (σ (B (n + 1)) * ι y) * ι y ^ n := by rw [pow_succ', mul_assoc]
      _ = (ι y * σ (B (n + 1)) - c • σ (B n)) * ι y ^ n := by rw [hcomm]
      _ = ι y * (σ (B (n + 1)) * ι y ^ n) - c • (σ (B n) * ι y ^ n) := by
          rw [sub_mul, mul_assoc, smul_mul_assoc]
      _ = ι y * (σ (B (n + 1)) * ι y ^ n) - c • (ι (((-c) ^ n : ℤ) : A) + ι y * γ) := by
          rw [hγ]
      _ = ι (((-c) ^ (n + 1) : ℤ) : A) + ι y * (σ (B (n + 1)) * ι y ^ n - c • γ) := by
          have hc' : ι (((-c) ^ (n + 1) : ℤ) : A) = -(c • ι (((-c) ^ n : ℤ) : A)) := by
            rw [← map_zsmul, ← map_neg, zsmul_eq_mul, ← Int.cast_mul, ← Int.cast_neg, pow_succ,
              mul_neg, mul_comm]
          rw [hc', mul_sub, smul_add, mul_smul_comm]
          abel

/-- **Main Theorem (algebraic form).** Let `ι : A → Γ` be a ring homomorphism from a commutative
ring, `ev : Γ → A` a left `A`-linear additive map with `ev 1 = 1`, `aug : A → S` a ring
homomorphism to a slender domain, `x ∈ A` with `aug x = 0`, `c` an integer with `c ≠ 0` in `S`,
`B : ℕ → Γ` with `B 0 = 1` and `B (n+1) ι(x) = ι(x) B (n+1) + c B n`, and `Y : ℤ^ℕ → Γ` a
homomorphism with `Y eₙ = ι(x)ⁿ B n`. Then `Γ` has no antiautomorphism `σ` with
`σ (ι A) = ι A`. -/
theorem not_exists_isRingAntiAut {A Γ S : Type*} [CommRing A] [Ring Γ] [CommRing S]
    [NoZeroDivisors S] (hS : Slender.{0} S)
    (ι : A →+* Γ) (ev : Γ →+ A)
    (hev_mul : ∀ (a : A) (γ : Γ), ev (ι a * γ) = a * ev γ) (hev_one : ev 1 = 1)
    (aug : A →+* S) (x : A) (hx : aug x = 0)
    (c : ℤ) (hc : (c : S) ≠ 0)
    (B : ℕ → Γ) (hB0 : B 0 = 1)
    (hB : ∀ n, B (n + 1) * ι x = ι x * B (n + 1) + c • B n)
    (Y : (ℕ → ℤ) →+ Γ) (hY : ∀ n, Y (Pi.single n 1) = ι x ^ n * B n) :
    ¬ ∃ σ : Γ → Γ, IsRingAntiAut σ ∧ σ '' Set.range ι = Set.range ι := by
  rintro ⟨σ, hσ, hrange⟩
  -- `ι` is injective, since `ev ∘ ι = id`
  have hevι : ∀ a, ev (ι a) = a := fun a => by
    have := hev_mul a 1
    rwa [mul_one, hev_one, mul_one] at this
  have hι : Function.Injective ι := fun a b hab => by rw [← hevι a, hab, hevι]
  -- `σ` as an additive homomorphism
  let σ' : Γ →+ Γ := AddMonoidHom.mk' σ hσ.map_add
  have hσ'_mul : ∀ a b, σ' (a * b) = σ' b * σ' a := hσ.map_mul_rev
  -- the restriction `τ` of `σ` to `A`
  have hτ : ∀ a, ∃ b, ι b = σ (ι a) := fun a => by
    have : σ (ι a) ∈ Set.range ι := hrange ▸ ⟨ι a, ⟨a, rfl⟩, rfl⟩
    exact this
  choose τ hτ using hτ
  let τ' : A →+* A :=
    { toFun := τ
      map_one' := hι (by rw [hτ, map_one, hσ.map_one])
      map_mul' := fun a b => hι (by
        rw [hτ, map_mul, hσ.map_mul_rev, ← hτ, ← hτ, ← map_mul, mul_comm])
      map_zero' := hι (by rw [hτ, map_zero]; exact map_zero σ')
      map_add' := fun a b => hι (by rw [hτ, map_add, hσ.map_add, ← hτ, ← hτ, ← map_add]) }
  have hτ_bij : Function.Bijective τ' := by
    constructor
    · intro a b hab
      apply hι
      apply hσ.bijective.1
      rw [← hτ, ← hτ]
      exact congrArg ι hab
    · intro b
      have : ι b ∈ σ '' Set.range ι := hrange.symm ▸ ⟨b, rfl⟩
      obtain ⟨_, ⟨a, rfl⟩, ha⟩ := this
      exact ⟨a, hι (by rw [← ha]; exact hτ a)⟩
  let e : A ≃+* A := RingEquiv.ofBijective τ' hτ_bij
  have he : ∀ a, e a = τ a := fun a => rfl
  -- the homomorphism `s = aug ∘ τ⁻¹ : A → S`
  let s : A →+* S := aug.comp e.symm.toRingHom
  have hs_x : ∀ u : A, s (τ x * u) = 0 := fun u => by
    have hx' : e.symm (τ x) = x := by rw [← he, e.symm_apply_apply]
    simp [s, hx', hx]
  -- powers of `ι x` under `σ`
  set y := τ x with hy
  have hxy : σ' (ι x) = ι y := (hτ x).symm
  have hpow : ∀ n, σ' (ι x ^ n) = ι y ^ n := by
    intro n
    induction n with
    | zero => simp [σ', hσ.map_one]
    | succ n ih => rw [pow_succ, hσ'_mul, ih, hxy, pow_succ']
  -- the key computation: `s (ev (σ (x ^ n B n))) = (-c) ^ n`
  have key : ∀ n, s (ev (σ' (Y (Pi.single n 1)))) = ((-c) ^ n : ℤ) := by
    intro n
    obtain ⟨γ, hγ⟩ := exists_antiAut_mul_pow_eq ι σ' hσ'_mul hσ.map_one x y hxy c B hB0 hB n
    rw [hY, hσ'_mul, hpow, hγ, map_add, hevι, hev_mul, map_add, map_intCast, hs_x, add_zero]
  -- contradiction with the Proposition
  have hfin := finite_of_weakSlender hS.weakSlender Y σ' ev s.toAddMonoidHom
  have huniv : {n : ℕ | s.toAddMonoidHom (ev (σ' (Y (Pi.single n 1)))) ≠ 0} = Set.univ := by
    refine Set.eq_univ_of_forall fun n => ?_
    have hn : s.toAddMonoidHom (ev (σ' (Y (Pi.single n 1)))) = ((-c) ^ n : ℤ) := key n
    rw [Set.mem_ofPred_eq, hn, Int.cast_pow, Int.cast_neg]
    exact pow_ne_zero _ (neg_ne_zero.mpr hc)
  rw [huniv] at hfin
  exact Set.infinite_univ hfin

/-- **Theorem (case `E = MU`).** With `A = MU_*`, `Γ = MU^*MU`, `S = ℤ`, `x = x₁`, `c = 2`,
`B n = B_n` the dual of `b₁ⁿ`, and `Y a = ∑ₙ aₙ x₁ⁿ B_n`, the ring `MU^*MU` has no
antiautomorphism preserving `MU^*`. Sources for the hypotheses (see the module docstring):
`MU_*MU = π[b₁, b₂, …]` [Bo, Thm. 8.2]; `MU^*MU ≅ Hom_π(MU_*MU, π)` as rings and bimodules
[Bo, Thm. 4.2, Thm. 5.4, Lemma 6.1]; `ev` left `π`-linear with `ev 1 = 1` [Bo, Lemma 3.4(a),
Lemma 5.6]; `η_R(x₁) = x₁ + 2b₁` from [Bo, (8.6)] and `εbᵢ = 0` for `i > 0` [Bo, Def. 8.1]. -/
theorem not_exists_isRingAntiAut_MU {A Γ : Type*} [CommRing A] [Ring Γ]
    (ι : A →+* Γ) (ev : Γ →+ A)
    (hev_mul : ∀ (a : A) (γ : Γ), ev (ι a * γ) = a * ev γ) (hev_one : ev 1 = 1)
    (aug : A →+* ℤ) (x : A) (hx : aug x = 0)
    (B : ℕ → Γ) (hB0 : B 0 = 1)
    (hB : ∀ n, B (n + 1) * ι x = ι x * B (n + 1) + (2 : ℤ) • B n)
    (Y : (ℕ → ℤ) →+ Γ) (hY : ∀ n, Y (Pi.single n 1) = ι x ^ n * B n) :
    ¬ ∃ σ : Γ → Γ, IsRingAntiAut σ ∧ σ '' Set.range ι = Set.range ι :=
  not_exists_isRingAntiAut slender_int ι ev hev_mul hev_one aug x hx 2 (by norm_num) B hB0 hB Y hY

/-- **Theorem (case `E = BP`).** With `A = BP_*`, `Γ = BP^*BP`, `S = ℤ₍ₚ₎`, `x = v₁`, `c = p`,
`B n = T_n` the dual of `t₁ⁿ`, and `Y a = ∑ₙ aₙ v₁ⁿ T_n`, the ring `BP^*BP` has no
antiautomorphism preserving `BP^*`. Sources for the hypotheses (see the module docstring):
`BP_*BP = π[t₁, t₂, …]` [Bo, Thm. 9.4]; `BP^*BP ≅ Hom_π(BP_*BP, π)` as rings and bimodules
[Bo, Thm. 4.2, Thm. 5.4, Lemma 6.1]; `ev` as in the `MU` case [Bo, Lemma 3.4(a), Lemma 5.6];
`η_R(v₁) = v₁ + p t₁` for the Hazewinkel generators from [Bo, (9.1), (9.3)]
(cf. [Ra, (A2.2.1), Thm. 4.1.18(iv)]). -/
theorem not_exists_isRingAntiAut_BP (p : ℕ) [Fact p.Prime] {A Γ : Type*} [CommRing A] [Ring Γ]
    (ι : A →+* Γ) (ev : Γ →+ A)
    (hev_mul : ∀ (a : A) (γ : Γ), ev (ι a * γ) = a * ev γ) (hev_one : ev 1 = 1)
    (aug : A →+* IntLocalAtPrime p) (x : A) (hx : aug x = 0)
    (B : ℕ → Γ) (hB0 : B 0 = 1)
    (hB : ∀ n, B (n + 1) * ι x = ι x * B (n + 1) + (p : ℤ) • B n)
    (Y : (ℕ → ℤ) →+ Γ) (hY : ∀ n, Y (Pi.single n 1) = ι x ^ n * B n) :
    ¬ ∃ σ : Γ → Γ, IsRingAntiAut σ ∧ σ '' Set.range ι = Set.range ι :=
  not_exists_isRingAntiAut (slender_intLocalAtPrime p) ι ev hev_mul hev_one aug x hx p
    (by exact_mod_cast (Nat.cast_ne_zero (R := IntLocalAtPrime p)).mpr (Fact.out : p.Prime).ne_zero)
    B hB0 hB Y hY

/-!
### The final Remark of the note

The note remarks that an analogous argument applies to the motivic spectra `MGL` and `BP` over
any base field. This will be addressed later.
-/

#print axioms not_exists_isRingAntiAut_MU
#print axioms not_exists_isRingAntiAut_BP

end BoardmanConjecture
