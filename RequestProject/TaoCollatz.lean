import Mathlib

/-!
# Tao's Collatz theorem (Theorem 1.3): a Lean port of the genuine-density core

This file is a self-contained Lean formalization mirroring the Idris2 development
in `TaoCollatz/` (in particular `TaoCollatz/MinimalProof.idr`).

The central theorem (Theorem 1.3 of `taocollatz.pdf`, "almost all Collatz orbits
attain almost bounded values") is stated with a **genuine natural-density**
notion of "almost all".

What is proved here without any assumptions:

* the elementary Collatz dynamics: iterating the Collatz map from `n` reaches the
  odd part of `n` (`collatz_drop`), and one Syracuse step is the odd part of the
  `3·+1` map;
* the **odd-part / Syracuse orbit simulation** (`colBelow_of_syrBelow`): if the
  Syracuse orbit of the odd part of `n` drops below a bound, so does the Collatz
  orbit of `n` itself — genuine dynamics, no assumptions;
* the **central reduction** (`theorem13GenuineFromSyracuse`): from a single
  honest analytic input, the genuine main theorem follows;
* a **non-degeneracy** corollary (`Theorem13Genuine.exists_mem`) showing the
  density-one good set is non-empty, so the conclusion is not vacuous.

The single deep analytic input — the density form of Tao's Theorem 1.6 for the
Syracuse map (`SyracuseDensityControl`) — is left as an explicit hypothesis,
because inhabiting it is exactly the hard analytic content of the paper
(Propositions 1.9 / 7.8 and the density transfer). Mirroring the Idris
development, it is a genuine, non-vacuous proposition, not a fabricated axiom.

We identify a positive integer with its value `n : ℕ` (the value `0` plays the
role of a trivial base point, exactly as `MkPos 0` does in the Idris code).
-/

open Filter Topology

namespace TaoCollatzLean

/-! ## Dynamics -/

/-- The Collatz map: halve if even, else `3·+1`. -/
def collatz (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Fuelled extraction of the odd factor: repeatedly halve while even. -/
def oddFactorFuel : ℕ → ℕ → ℕ
  | 0, n => n
  | (f + 1), n => if n % 2 = 0 then oddFactorFuel f (n / 2) else n

/-- The odd part of `n` (the largest odd divisor; `oddFactor 0 = 0`). -/
def oddFactor (n : ℕ) : ℕ := oddFactorFuel n n

/-- Fuelled count of halving steps performed by `oddFactorFuel`. -/
def dropTimeFuel : ℕ → ℕ → ℕ
  | 0, _ => 0
  | (f + 1), n => if n % 2 = 0 then dropTimeFuel f (n / 2) + 1 else 0

/-- The number of Collatz steps needed to reach the odd part of `n`. -/
def dropTime (n : ℕ) : ℕ := dropTimeFuel n n

/-- The Syracuse map on odd numbers: the odd part of `3n+1`. -/
def syr (n : ℕ) : ℕ := oddFactor (3 * n + 1)

/-- `EventuallyBelow step start bound`: iterating `step` from `start` eventually
reaches a value `≤ bound`. -/
def EventuallyBelow (step : ℕ → ℕ) (start bound : ℕ) : Prop :=
  ∃ t, step^[t] start ≤ bound

/-- The Collatz orbit of `n` eventually drops to `≤ bound`. -/
def ColBelow (n bound : ℕ) : Prop := EventuallyBelow collatz n bound

/-- The Syracuse orbit of the odd number `n` eventually drops to `≤ bound`. -/
def SyrBelow (n bound : ℕ) : Prop := EventuallyBelow syr n bound

/-! ## Genuine elementary dynamics -/

/-
Iterating Collatz for `dropTimeFuel f n` steps reaches `oddFactorFuel f n`,
for every fuel budget.
-/
theorem collatz_dropFuel (f n : ℕ) :
    collatz^[dropTimeFuel f n] n = oddFactorFuel f n := by
  induction' f with f ih generalizing n;
  · rfl;
  · by_cases h : n % 2 = 0 <;> simp +decide [ h, dropTimeFuel, oddFactorFuel ];
    rw [ ← ih, show collatz n = n / 2 from by rw [ collatz ] ; aesop ]

/-- Iterating the Collatz map from `n` reaches the odd part of `n`. -/
theorem collatz_drop (n : ℕ) : collatz^[dropTime n] n = oddFactor n :=
  collatz_dropFuel n n

/-
The odd part of a positive number is odd.
-/
theorem oddFactor_odd (n : ℕ) (hn : 0 < n) : oddFactor n % 2 = 1 := by
  have h_odd_factor : ∀ f n, 0 < n → n ≤ f → oddFactorFuel f n % 2 = 1 := by
    intro f n hn hf; induction' f with f ih generalizing n <;> simp_all +arith +decide;
    by_cases h : n % 2 = 0 <;> simp_all +arith +decide [ oddFactorFuel ];
    exact ih _ ( Nat.div_pos ( Nat.le_of_dvd hn ( Nat.dvd_of_mod_eq_zero h ) ) zero_lt_two ) ( Nat.le_of_lt_succ ( by omega ) );
  exact h_odd_factor n n hn le_rfl

/-
One Collatz step on an odd number is the `3·+1` map.
-/
theorem collatz_odd (m : ℕ) (hm : m % 2 = 1) : collatz m = 3 * m + 1 := by
  exact if_neg ( by aesop )

/-
Every Syracuse step lands on an odd number.
-/
theorem syr_odd (m : ℕ) : syr m % 2 = 1 := by
  convert oddFactor_odd ( 3 * m + 1 ) ( Nat.succ_pos _ ) using 1

/-
**Realisation of the Syracuse orbit inside the Collatz orbit**, starting from
an odd number: every Syracuse iterate is a Collatz iterate.
-/
theorem syrRealize (m : ℕ) (hm : m % 2 = 1) (t : ℕ) :
    ∃ s, collatz^[s] m = syr^[t] m := by
  induction' t with t ih generalizing m;
  · exact ⟨ 0, rfl ⟩;
  · obtain ⟨ s, hs ⟩ := ih ( oddFactor ( 3 * m + 1 ) ) ( by
      exact oddFactor_odd _ ( Nat.succ_pos _ ) );
    use s + dropTime ( 3 * m + 1 ) + 1;
    simp_all +decide [ Function.iterate_add_apply ];
    rw [ collatz_odd m hm, collatz_drop ] ; aesop

/-
**The odd-part orbit simulation height bound**: for every start `n` and every
Syracuse time `t`, some Collatz iterate of `n` is `≤` the `t`-th Syracuse iterate
of the odd part of `n`.
-/
theorem oddPartHeightBound (n t : ℕ) :
    ∃ s, collatz^[s] n ≤ syr^[t] (oddFactor n) := by
  by_cases hn : n = 0;
  · use 0; simp [hn];
  · obtain ⟨ s', hs' ⟩ := syrRealize ( oddFactor n ) ( oddFactor_odd n ( Nat.pos_of_ne_zero hn ) ) t;
    exact ⟨ s' + dropTime n, by rw [ Function.iterate_add_apply, collatz_drop ] ; exact hs'.le ⟩

/-- **The odd-part orbit simulation transfer**: if the Syracuse orbit of the odd
part of `n` drops below a bound, so does the Collatz orbit of `n`. -/
theorem colBelow_of_syrBelow (n bound : ℕ) :
    SyrBelow (oddFactor n) bound → ColBelow n bound := by
  rintro ⟨t, ht⟩
  obtain ⟨s, hs⟩ := oddPartHeightBound n t
  exact ⟨s, le_trans hs ht⟩

/-! ## The 2-adic valuation, Syracuse factorisation and the exact affine backbone

These are the genuinely-provable arithmetic ingredients of the Syracuse
first-passage analysis (mirroring `TaoCollatz/Pieces64.idr`, `StepArith.idr`,
`StepArith2.idr` and the `affineBackbone` in `TaoCollatz/HoleProof.idr`). -/

/-
Reconstruction of a number from its odd part and its halving count, fuelled:
`2^{dropTimeFuel f n} · oddFactorFuel f n = n`, for every fuel budget.
-/
theorem reconstructFuel (f n : ℕ) :
    2 ^ (dropTimeFuel f n) * oddFactorFuel f n = n := by
      induction' f with f ih generalizing n;
      · -- In the base case where `f = 0`, `dropTimeFuel 0 n` is 0 and `oddFactorFuel 0 n` is `n`.
        simp [dropTimeFuel, oddFactorFuel];
      · by_cases h : n % 2 = 0 <;> simp_all +decide [ dropTimeFuel, oddFactorFuel ];
        rw [ pow_succ', mul_assoc, ih, ← Nat.dvd_iff_mod_eq_zero ] at * ; obtain ⟨ k, hk ⟩ := ‹_› ; simp_all +decide

/-- Reconstruction: `2^{dropTime n} · oddFactor n = n`. -/
theorem reconstruct (n : ℕ) : 2 ^ dropTime n * oddFactor n = n :=
  reconstructFuel n n

/-- The 2-adic valuation appearing in one Syracuse step: `a(n)` is the number of
halvings taken to pass from `3n+1` to its odd part. -/
def syrVal (n : ℕ) : ℕ := dropTime (3 * n + 1)

/-- **One-step Syracuse factorisation**: `2^{a(n)} · syr n = 3n + 1`. -/
theorem syr_factorization (n : ℕ) : 2 ^ syrVal n * syr n = 3 * n + 1 :=
  reconstruct (3 * n + 1)

/-- `syrValSum k x = a_1(x) + ⋯ + a_k(x)`, the sum of the first `k` Syracuse
2-adic valuations along the orbit of `x`. -/
def syrValSum : ℕ → ℕ → ℕ
  | 0, _ => 0
  | (k + 1), x => syrVal x + syrValSum k (syr x)

/-
**The exact affine backbone (step 3)**: for every start `x` and every number
of Syracuse steps `n`, there is an affine correction `c` with
`2^{S_n(x)} · Syr^n(x) = 3^n · x + c`, where `S_n(x) = syrValSum n x`.
-/
theorem affineBackbone (x n : ℕ) :
    ∃ c, 2 ^ (syrValSum n x) * syr^[n] x = 3 ^ n * x + c := by
  induction n generalizing x with
  | zero => exact ⟨0, by simp [syrValSum]⟩
  | succ n ih =>
    obtain ⟨c', hc'⟩ := ih (syr x)
    refine ⟨3 ^ n + 2 ^ syrVal x * c', ?_⟩
    rw [Function.iterate_succ_apply,
        show syrValSum (n + 1) x = syrVal x + syrValSum n (syr x) from rfl,
        pow_add, mul_assoc, hc', mul_add, ← mul_assoc,
        mul_comm (2 ^ syrVal x) (3 ^ n), mul_assoc, syr_factorization x]
    ring

/-
**Strict five-step growth comparison (seed of step 1)**: `3^5 < 2^8`
(i.e. `243 < 256`).
-/
theorem strictGrowth : 3 ^ 5 < 2 ^ 8 := by
  norm_num

/-
**Iterated growth (step 2)**: `3^{5k} ≤ 2^{8k}` for every `k`.
-/
theorem iteratedGrowth (k : ℕ) : 3 ^ (5 * k) ≤ 2 ^ (8 * k) := by
  simpa only [ pow_mul ] using Nat.pow_le_pow_left ( by decide ) _

/-
Linear-beats-exponential bound: `243^n · n ≤ 243 · 256^n`.
-/
theorem pow243_linear (n : ℕ) : 243 ^ n * n ≤ 243 * 256 ^ n := by
  induction' n with n ih;
  · norm_num;
  · ring_nf at *;
    nlinarith [ pow_pos ( show 0 < 243 by norm_num ) n, pow_le_pow_left' ( show 243 ≤ 256 by norm_num ) n ]

/-
If `243 · z ≤ n` then `243^n · z ≤ 256^n`.
-/
theorem pow243_z (n z : ℕ) (h : 243 * z ≤ n) : 243 ^ n * z ≤ 256 ^ n := by
  nlinarith [ pow_pos ( show 0 < 243 by norm_num ) n, pow_pos ( show 0 < 256 by norm_num ) n, pow243_linear n ]

/-
**Contraction arithmetic (core of step 5)**: if the drift budget `n` beats
`243 · fy^5` and the valuation sum `sn` realises the `8/5` drift rate, then the
growth `3^n · fy` is dominated by the contraction `2^{sn}`.
-/
theorem contractionArith (n fy sn : ℕ)
    (hbig : 243 * fy ^ 5 ≤ n) (hdrift : 8 * n ≤ 5 * sn) :
    3 ^ n * fy ≤ 2 ^ sn := by
      have h_cont : 3^(5*n) * fy^5 ≤ 2^(5*sn) := by
        rw [ pow_mul ];
        refine le_trans ?_ ( pow_le_pow_right₀ ( by decide ) hdrift );
        convert pow243_z n ( fy ^ 5 ) hbig using 1 ; norm_num [ pow_mul ];
      contrapose! h_cont;
      convert Nat.pow_lt_pow_left h_cont ( by norm_num : 5 ≠ 0 ) using 1 <;> ring

/-! ## Genuine 2-adic valuation distribution (content of Proposition 1.9)

The exact 2-adic valuation tail of the one-step Syracuse map.  These are
fully-proved distributional facts (mirroring the Idris `ValuationTail` /
`GenuineEstimates` modules): the number of Syracuse halvings `syrVal x` is
governed 2-adically by `3x+1`, giving the exact geometric valuation tail that
underlies the drift.  (The density-one *law of large numbers* built on top of
this — `step4_valuationLowerBound` — remains the deep analytic hole.) -/

/-
`dropTimeFuel` computes the 2-adic valuation once the fuel is large enough:
for `0 < m` and `m ≤ f`, `j ≤ dropTimeFuel f m ↔ 2^j ∣ m`.
-/
theorem dropTimeFuel_ge_iff (f m j : ℕ) (hm : 0 < m) (hf : m ≤ f) :
    j ≤ dropTimeFuel f m ↔ 2 ^ j ∣ m := by
      revert j;
      induction' f with f ih generalizing m;
      · linarith;
      · rcases Nat.even_or_odd' m with ⟨ k, rfl | rfl ⟩;
        · intro j; specialize ih k ( by linarith ) ( by linarith ) ;
          rcases j with ( _ | j ) <;> simp_all +decide [ Nat.pow_succ', Nat.mul_dvd_mul_iff_left ];
          rw [ show dropTimeFuel ( f + 1 ) ( 2 * k ) = dropTimeFuel f k + 1 from ?_ ];
          · rw [ Nat.lt_succ_iff, ih ];
          · exact if_pos ( by norm_num ) |> fun h => h.trans ( by norm_num );
        · intro j; rw [ show dropTimeFuel ( f + 1 ) ( 2 * k + 1 ) = 0 from by { exact if_neg ( by norm_num [ Nat.add_mod ] ) } ] ; rcases j with ( _ | j ) <;> simp +decide [ Nat.pow_succ' ] ;
          exact fun h => by have := congr_arg ( · % 2 ) h.choose_spec; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at this;

/-- `dropTime m` is the 2-adic valuation of `m` (for `m > 0`): `j ≤ dropTime m`
iff `2^j` divides `m`. -/
theorem dropTime_ge_iff (m j : ℕ) (hm : 0 < m) :
    j ≤ dropTime m ↔ 2 ^ j ∣ m :=
  dropTimeFuel_ge_iff m m j hm le_rfl

/-- The one-step Syracuse valuation tail: `j ≤ syrVal x` iff `2^j ∣ 3x+1`. -/
theorem syrVal_ge_iff (x j : ℕ) : j ≤ syrVal x ↔ 2 ^ j ∣ (3 * x + 1) :=
  dropTime_ge_iff (3 * x + 1) j (Nat.succ_pos _)

/-
The one-step Syracuse valuation is `1` exactly on `x ≡ 3 (mod 4)`.
-/
theorem syrVal_eq_one_iff (x : ℕ) (hx : x % 2 = 1) : syrVal x = 1 ↔ x % 4 = 3 := by
  constructor <;> intro h;
  · have := syrVal_ge_iff x 2; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ; ( rw [ ← Nat.mod_mod_of_dvd x ( by decide : 2 ∣ 4 ) ] at hx; ( have := Nat.mod_lt x zero_lt_four; interval_cases _ : x % 4 <;> simp_all +decide ; ) );
    grind;
  · refine' le_antisymm _ _ <;> norm_num [ syrVal_ge_iff ];
    · exact Nat.le_of_not_lt fun h' => by have := syrVal_ge_iff x 2; norm_num at this; omega;
    · omega

/-
**Exact geometric valuation tail**: in one full period `range (2^j)` there is
exactly one residue with `syrVal x ≥ j` (necessarily odd), for `j ≥ 1`.  This is
the exact survival function `μ({a ≥ j}) · 2^j = 1` of Tao's Proposition 1.9.
-/
theorem syrVal_tail_count (j : ℕ) (hj : 1 ≤ j) :
    (Finset.filter (fun x => x % 2 = 1 ∧ j ≤ syrVal x) (Finset.range (2 ^ j))).card = 1 := by
      obtain ⟨x, hx⟩ : ∃ x ∈ Finset.range (2 ^ j), x % 2 = 1 ∧ j ≤ syrVal x := by
        obtain ⟨x, hx⟩ : ∃ x ∈ Finset.range (2 ^ j), 2 ^ j ∣ (3 * x + 1) := by
          -- By definition of modular arithmetic, there exists an $x$ such that $3x \equiv -1 \pmod{2^j}$.
          have h_mod : ∃ x, 3 * x ≡ 2 ^ j - 1 [MOD 2 ^ j] := by
            -- By definition of modular arithmetic, there exists an $x$ such that $3x \equiv 1 \pmod{2^j}$.
            have h_mod : ∃ x, 3 * x ≡ 1 [MOD 2 ^ j] := by
              exact ⟨ 3 ^ ( Nat.totient ( 2 ^ j ) - 1 ), by rw [ ← pow_succ', Nat.sub_add_cancel ( Nat.succ_le_iff.mpr ( Nat.totient_pos.mpr ( by positivity ) ) ) ] ; exact Nat.ModEq.pow_totient ( by cases j <;> norm_num at * ) ⟩;
            exact ⟨ h_mod.choose * ( 2 ^ j - 1 ), by simpa [ mul_assoc ] using h_mod.choose_spec.mul_right _ ⟩;
          obtain ⟨ x, hx ⟩ := h_mod; use x % ( 2 ^ j ) ; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ] ;
          exact ⟨ Nat.mod_lt _ ( by positivity ), by rw [ ← ZMod.natCast_eq_zero_iff ] ; simp_all +decide ⟩;
        use x;
        exact ⟨ hx.1, Nat.mod_two_ne_zero.mp fun h => by have := Nat.dvd_trans ( dvd_pow_self _ ( by linarith ) ) hx.2; norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, h ] at this, syrVal_ge_iff x j |>.2 hx.2 ⟩;
      -- If there were another $y$ in the set, then $y$ would also satisfy $y \equiv x \pmod{2^j}$.
      have h_unique : ∀ y ∈ Finset.range (2 ^ j), y % 2 = 1 ∧ j ≤ syrVal y → y ≡ x [MOD 2 ^ j] := by
        intros y hy hy_cond
        have h_div : 2 ^ j ∣ (3 * y + 1) ∧ 2 ^ j ∣ (3 * x + 1) := by
          exact ⟨ syrVal_ge_iff _ _ |>.1 hy_cond.2, syrVal_ge_iff _ _ |>.1 hx.2.2 ⟩;
        have h_cong : 3 * y ≡ 3 * x [MOD 2 ^ j] := by
          rw [ Nat.modEq_iff_dvd ];
          simpa using dvd_sub ( Int.natCast_dvd_natCast.mpr h_div.2 ) ( Int.natCast_dvd_natCast.mpr h_div.1 );
        rw [ Nat.modEq_iff_dvd ] at *;
        norm_num [ ← mul_sub ] at *;
        exact ( Int.dvd_of_dvd_mul_right_of_gcd_one h_cong <| by cases j <;> norm_num [ Int.gcd, Int.natAbs_pow ] at * );
      exact Finset.card_eq_one.mpr ⟨ x, Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_filter.mpr ⟨ hx.1, hx.2 ⟩, fun y hy => Nat.mod_eq_of_lt ( Finset.mem_range.mp ( Finset.mem_filter.mp hy |>.1 ) ) ▸ Nat.mod_eq_of_lt ( Finset.mem_range.mp hx.1 ) ▸ h_unique y ( Finset.mem_filter.mp hy |>.1 ) ( Finset.mem_filter.mp hy |>.2 ) ⟩ ⟩

/-
**Exact geometric valuation tail over a full period `2^K`**: for `1 ≤ j ≤ K`,
there are exactly `2^(K-j)` residues `x` in `range (2^K)` with `syrVal x ≥ j`
(all necessarily odd).  This strengthens `syrVal_tail_count` (the `K = j` case,
where `2^(K-j) = 1`) to arbitrary period length, giving the exact survival
function `μ({a ≥ j}) = 2^{-j}` of Tao's Proposition 1.9 across a genuine period.
The count is `2^(K-j)` because `2^j ∣ 3x+1` pins `x` to a single residue class
mod `2^j` (as `3` is invertible mod `2^j`), and that class meets `range (2^K)`
in exactly `2^(K-j)` points.
-/
theorem syrVal_tail_count_period (K j : ℕ) (hj : 1 ≤ j) (hjK : j ≤ K) :
    (Finset.filter (fun x => x % 2 = 1 ∧ j ≤ syrVal x) (Finset.range (2 ^ K))).card
      = 2 ^ (K - j) := by
        -- We count x in range(2^K) with x%2=1 and j ≤ syrVal x using the fact that 2^j ∣ 3x+1.
        have h_count : (Finset.filter (fun x => 2 ^ j ∣ 3 * x + 1) (Finset.range (2 ^ K))).card = 2 ^ (K - j) := by
          -- The congruence $3x + 1 \equiv 0 \pmod{2^j}$ has a unique solution modulo $2^j$.
          obtain ⟨r, hr⟩ : ∃ r : ℕ, r < 2 ^ j ∧ 3 * r + 1 ≡ 0 [MOD 2 ^ j] := by
            -- We need to find an $r$ such that $3r \equiv -1 \pmod{2^j}$.
            have h_cong : ∃ r, 3 * r ≡ -1 [ZMOD 2 ^ j] := by
              -- Since $3$ and $2^j$ are coprime, $3$ has an inverse modulo $2^j$.
              have h_inv : ∃ x : ℤ, 3 * x ≡ 1 [ZMOD 2 ^ j] := by
                exact ⟨ 3 ^ ( Nat.totient ( 2 ^ j ) - 1 ), by rw [ ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr <| by positivity ) ] ; exact by simpa [ ← Int.natCast_modEq_iff ] using Nat.ModEq.pow_totient <| Nat.coprime_comm.mp <| Nat.Coprime.pow_left _ <| by decide ⟩;
              exact ⟨ -h_inv.choose, by convert h_inv.choose_spec.neg using 1; ring ⟩;
            obtain ⟨ r, hr ⟩ := h_cong;
            exact ⟨ Int.toNat ( r % ( 2 ^ j ) ), by linarith [ Int.emod_lt_of_pos r ( by positivity : 0 < ( 2 ^ j : ℤ ) ), Int.toNat_of_nonneg ( Int.emod_nonneg r ( by positivity : ( 2 ^ j : ℤ ) ≠ 0 ) ) ], by simpa [ ← Int.natCast_modEq_iff, Int.ModEq, Int.add_emod, Int.mul_emod, Int.toNat_of_nonneg ( Int.emod_nonneg r ( by positivity : ( 2 ^ j : ℤ ) ≠ 0 ) ) ] using hr.add_right 1 ⟩;
          -- The set of solutions to $3x + 1 \equiv 0 \pmod{2^j}$ in the range $0$ to $2^K - 1$ is exactly $\{r + k \cdot 2^j \mid k = 0, 1, \ldots, 2^{K-j} - 1\}$.
          have h_solutions : Finset.filter (fun x => 2 ^ j ∣ 3 * x + 1) (Finset.range (2 ^ K)) = Finset.image (fun k => r + k * 2 ^ j) (Finset.range (2 ^ (K - j))) := by
            ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image];
            constructor <;> intro hx;
            · -- Since $3x + 1 \equiv 0 \pmod{2^j}$, we have $x \equiv r \pmod{2^j}$.
              have h_cong : x ≡ r [MOD 2 ^ j] := by
                have h_cong : 3 * x ≡ 3 * r [MOD 2 ^ j] := by
                  rw [ Nat.modEq_iff_dvd ] at *;
                  obtain ⟨ k, hk ⟩ := hx.2; obtain ⟨ l, hl ⟩ := hr.2; use -k - l; push_cast at *; linarith;
                rw [ Nat.modEq_iff_dvd ] at *;
                exact ( Int.dvd_of_dvd_mul_right_of_gcd_one ( by simpa [ mul_sub ] using h_cong ) <| by cases j <;> norm_num [ Int.gcd, Int.natAbs_pow ] at * );
              rw [ ← Nat.mod_add_div x ( 2 ^ j ), h_cong ];
              exact ⟨ x / 2 ^ j, Nat.div_lt_of_lt_mul <| by rw [ mul_comm, ← pow_add, Nat.sub_add_cancel hjK ] ; linarith, by rw [ Nat.mod_eq_of_lt hr.1 ] ; ring ⟩;
            · rcases hx with ⟨ a, ha, rfl ⟩ ; rw [ show 2 ^ K = 2 ^ j * 2 ^ ( K - j ) by rw [ ← pow_add, Nat.add_sub_of_le hjK ] ] ; exact ⟨ by nlinarith, by rw [ Nat.dvd_iff_mod_eq_zero ] ; simpa [ Nat.ModEq, Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] using hr.2 ⟩ ;
          rw [ h_solutions, Finset.card_image_of_injective ] <;> aesop_cat;
        convert h_count using 2 ; ext x ; simp +decide [ syrVal_ge_iff ];
        intro hx h; have := Nat.dvd_trans ( pow_dvd_pow _ hj ) h; norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at this; have := Nat.mod_lt x two_pos; interval_cases x % 2 <;> simp_all +decide ;

/-
**Exact geometric valuation level counts over a full period `2^K`**: for
`1 ≤ j` with `j + 1 ≤ K`, there are exactly `2^(K-j-1)` residues `x` in
`range (2^K)` with `syrVal x = j` (all necessarily odd).  This is the exact
*probability mass function* `μ({a = j}) = 2^{-(j+1)}` of the geometric law of
Tao's Proposition 1.9, obtained from the tail counts by
`2^(K-j) - 2^(K-(j+1)) = 2^(K-j-1)`.
-/
theorem syrVal_level_count_period (K j : ℕ) (hj : 1 ≤ j) (hjK : j + 1 ≤ K) :
    (Finset.filter (fun x => x % 2 = 1 ∧ syrVal x = j) (Finset.range (2 ^ K))).card
      = 2 ^ (K - j - 1) := by
        -- The level set {x ∈ range(2^K) | syrVal x = j} equals the tail set {syrVal x ≥ j} minus the tail set {syrVal x ≥ j+1}.
        have h_level_set : Finset.filter (fun x => x % 2 = 1 ∧ syrVal x = j) (Finset.range (2 ^ K)) = Finset.filter (fun x => x % 2 = 1 ∧ j ≤ syrVal x) (Finset.range (2 ^ K)) \ Finset.filter (fun x => x % 2 = 1 ∧ j + 1 ≤ syrVal x) (Finset.range (2 ^ K)) := by
          grind;
        rw [ h_level_set, Finset.card_sdiff ];
        rw [ Finset.inter_eq_left.mpr ];
        · have := syrVal_tail_count_period K j hj ( by linarith ) ; have := syrVal_tail_count_period K ( j + 1 ) ( by linarith ) ( by linarith ) ; simp_all +decide [ Nat.sub_sub ] ;
          rw [ show K - j = K - ( j + 1 ) + 1 by omega, pow_succ' ] ; omega;
        · grind

/-! ## Genuine natural density -/

/-- A `Bool`-valued set `bad` has natural density zero. -/
def DensityZero (bad : ℕ → Bool) : Prop :=
  Tendsto
    (fun N : ℕ => ((Finset.filter (fun n => bad n = true) (Finset.range N)).card : ℝ) / N)
    atTop (𝓝 0)

/-- Genuine "almost all `n` satisfy `p`": there is a good set of density one
(its complement has density zero) contained in `{n | p n}`. -/
def AlmostAllSatisfy (p : ℕ → Prop) : Prop :=
  ∃ good : ℕ → Bool, DensityZero (fun n => !good n) ∧ ∀ n, good n = true → p n

/-- Monotonicity of almost-all along pointwise implication. -/
theorem AlmostAllSatisfy.mono {p q : ℕ → Prop} (h : ∀ n, p n → q n) :
    AlmostAllSatisfy p → AlmostAllSatisfy q := by
  rintro ⟨good, hd, hp⟩
  exact ⟨good, hd, fun n hn => h n (hp n hn)⟩

/-
The full set does not have density zero (its density is one).
-/
theorem not_densityZero_const_true : ¬ DensityZero (fun _ => true) := by
  intro h;
  have := h.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with N hN using by aesop ) ; norm_num at this;

/-- Non-degeneracy: an almost-all set is non-empty. -/
theorem AlmostAllSatisfy.exists_mem {p : ℕ → Prop} (h : AlmostAllSatisfy p) :
    ∃ n, p n := by
  obtain ⟨good, hd, hp⟩ := h
  by_contra hcon
  push_neg at hcon
  -- if no `n` satisfies `p`, then no `n` is good, so the complement is everything
  have hgood : ∀ n, good n = false := by
    intro n
    by_contra hn
    have : good n = true := by
      cases hb : good n with
      | false => exact absurd hb hn
      | true => rfl
    exact (hcon n (hp n this)).elim
  apply not_densityZero_const_true
  have : (fun n => !good n) = (fun _ : ℕ => true) := by
    funext n; rw [hgood n]; rfl
  rwa [this] at hd

/-! ## The main theorem and the single deep input -/

/-- `f` tends to infinity. -/
def TendsToInfinity (f : ℕ → ℕ) : Prop := Tendsto f atTop atTop

/-- **Theorem 1.3, genuine natural-density form**: for every height function `f`
tending to infinity, almost every `n` has a Collatz orbit that drops below
`f n`. -/
def Theorem13Genuine : Prop :=
  ∀ f : ℕ → ℕ, TendsToInfinity f → AlmostAllSatisfy (fun n => ColBelow n (f n))

/-- **The single deep analytic input** (density form of Tao's Theorem 1.6 for the
Syracuse map, transported along the odd-part map): for every `f` tending to
infinity there is a density-one set of `n` on which the Syracuse orbit of the odd
part of `n` drops below `f n`. This is the analytic heart of the paper and is
left as an explicit hypothesis. -/
def SyracuseDensityControl : Prop :=
  ∀ f : ℕ → ℕ, TendsToInfinity f →
    ∃ good : ℕ → Bool,
      DensityZero (fun n => !good n) ∧
      ∀ n, good n = true → SyrBelow (oddFactor n) (f n)

/-- **The central reduction, proved in full**: from the single honest Syracuse
density input, the genuine main theorem follows. -/
theorem theorem13GenuineFromSyracuse :
    SyracuseDensityControl → Theorem13Genuine := by
  intro control f hf
  obtain ⟨good, hd, hsyr⟩ := control f hf
  exact ⟨good, hd, fun n hn => colBelow_of_syrBelow n (f n) (hsyr n hn)⟩

/-- Non-degeneracy of the main theorem: the produced good set has a member, so
the conclusion is not vacuous. -/
theorem Theorem13Genuine.exists_mem (thm : Theorem13Genuine)
    (f : ℕ → ℕ) (hf : TendsToInfinity f) :
    ∃ n, ColBelow n (f n) :=
  (thm f hf).exists_mem

/-! ## Strict and paper-domain reformulations -/

/-- The strict-bound Collatz drop: the orbit drops *strictly* below `bound`
(defined, as in the Idris development, as dropping `≤ bound - 1`). -/
def ColBelowStrict (n bound : ℕ) : Prop := ColBelow n (bound - 1)

/-
If `f` tends to infinity, so does `n ↦ f n - 1`.
-/
theorem growthPred {f : ℕ → ℕ} (hf : TendsToInfinity f) :
    TendsToInfinity (fun n => f n - 1) := by
  exact Filter.tendsto_atTop_atTop.mpr fun C => by rcases Filter.eventually_atTop.mp ( hf.eventually_ge_atTop ( C + 1 ) ) with ⟨ k, hk ⟩ ; exact ⟨ k, fun n hn => Nat.le_sub_one_of_lt ( hk n hn ) ⟩ ;

/-- **Theorem 1.3, strict genuine-density form**: almost every `n` has its
Collatz orbit drop strictly below `f n`. -/
def Theorem13GenuineStrict : Prop :=
  ∀ f : ℕ → ℕ, TendsToInfinity f → AlmostAllSatisfy (fun n => ColBelowStrict n (f n))

/-- The strict form follows from the plain form applied to `n ↦ f n - 1`
(which still tends to infinity). -/
theorem theorem13GenuineStrictFromGenuine :
    Theorem13Genuine → Theorem13GenuineStrict :=
  fun thm f hf => thm (fun n => f n - 1) (growthPred hf)

/-- **Theorem 1.3 over the positive-integer domain**, strict genuine-density
form. -/
def Theorem13GenuinePaperDomain : Prop :=
  ∀ f : ℕ → ℕ, TendsToInfinity f →
    AlmostAllSatisfy (fun n => 0 < n → ColBelowStrict n (f n))

theorem theorem13GenuinePaperDomainFromStrict :
    Theorem13GenuineStrict → Theorem13GenuinePaperDomain :=
  fun thm f hf => (thm f hf).mono (fun _ below _ => below)

/-! ## The eight-step gate decomposition

Here we decompose the single deep analytic input `SyracuseDensityControl` into
the milestone chain of `TaoCollatz/HoleProof.idr` (steps 4-7 of the eight-step
gate).  The genuinely-arithmetic reductions are proved outright; the deep
analytic cores (the density/concentration content of Tao's argument, i.e. the
Idris holes `holeA7core`, `holeC7`, `holeD7`) are stated as explicit, honestly
typed `sorry` milestones.

All milestones are indexed by `n : ℕ` and speak about the odd start
`oddFactor n`, matching the way `SyracuseDensityControl` is already phrased. -/

/-- **Step 4 target** (large-deviation valuation drift, density form): for every
height `f → ∞` there is a density-one set of `n` on which the Syracuse valuation
sum of the odd part of `n` realises the `8/5` drift rate at some time `≥ f n`. -/
def ValuationLowerBoundDensity : Prop :=
  ∀ f : ℕ → ℕ, TendsToInfinity f →
    ∃ good : ℕ → Bool, DensityZero (fun n => !good n) ∧
      ∀ n, good n = true →
        ∃ m, f n ≤ m ∧ 8 * m ≤ 5 * syrValSum m (oddFactor n)

/-- **Step 5 target** (contraction dominates growth, density form). -/
def ContractionDominatesDensity : Prop :=
  ∀ f : ℕ → ℕ, TendsToInfinity f →
    ∃ good : ℕ → Bool, DensityZero (fun n => !good n) ∧
      ∀ n, good n = true →
        ∃ m, 3 ^ m * f n ≤ 2 ^ syrValSum m (oddFactor n)

/-- **Step 6 target** (typical descent below the starting value, density form).
The descent must occur at a *positive* time and be *strict* (`syr^[m] (oddFactor n)
< oddFactor n`); the trivial `m = 0` reading (`syr^[0] x = x`) is exactly the
degenerate case ruled out by the Idris hole `DescentPosTy`/`holeC7`, so admitting
it would make this milestone vacuously true. -/
def TypicalDescentDensity : Prop :=
  ∃ good : ℕ → Bool, DensityZero (fun n => !good n) ∧
    ∀ n, good n = true → ∃ m, 0 < m ∧ syr^[m] (oddFactor n) < oddFactor n

/-
**Step 5, proved reduction**: contraction dominance follows from the
valuation drift, by applying the drift at the inflated height
`g n = 243 · (f n)^5` and feeding the outcome to `contractionArith`.
-/
theorem step5_contractionFromValuation :
    ValuationLowerBoundDensity → ContractionDominatesDensity := by
      intro h f hf
      obtain ⟨good, hgood_zero, hgood⟩ := h (fun n => 243 * (f n)^5) (by
      exact Filter.tendsto_atTop_atTop.mpr fun x => by rcases Filter.eventually_atTop.mp ( hf.eventually_ge_atTop ( x + 1 ) ) with ⟨ y, hy ⟩ ; exact ⟨ y, fun n hn => by nlinarith [ hy n hn, pow_nonneg ( Nat.zero_le ( f n ) ) 2, pow_nonneg ( Nat.zero_le ( f n ) ) 3, pow_nonneg ( Nat.zero_le ( f n ) ) 4 ] ⟩ ;);
      exact ⟨ good, hgood_zero, fun n hn => by obtain ⟨ m, hm₁, hm₂ ⟩ := hgood n hn; exact ⟨ m, contractionArith m ( f n ) ( syrValSum m ( oddFactor n ) ) hm₁ hm₂ ⟩ ⟩

/-- **Step 4** (analytic hole, mirrors Idris `holeA7core`): the density-one
large-deviation drift of the Syracuse 2-adic valuation.  This is the
concentration / law-of-large-numbers heart of Tao's argument. -/
theorem step4_valuationLowerBound : ValuationLowerBoundDensity := by sorry

/-
**Step 6** (analytic hole, mirrors Idris `holeC7`): typical descent below
the starting value, from contraction dominance and the affine backbone.
-/
theorem step6_typicalDescent :
    ContractionDominatesDensity → TypicalDescentDensity := by sorry

/-- **Step 7** (analytic hole, mirrors Idris `holeD7`): the renewal / height
diagonalisation upgrading typical descent to density-one first passage below an
arbitrary height `f → ∞`. -/
theorem step7_oddControl :
    TypicalDescentDensity → SyracuseDensityControl := by sorry

/-- The single analytic gate, assembled from the eight steps.  Only the three
deep analytic milestones (`step4`, `step6`, `step7`) remain unproved. -/
theorem syracuseDensityControl : SyracuseDensityControl :=
  step7_oddControl
    (step6_typicalDescent
      (step5_contractionFromValuation step4_valuationLowerBound))

/-- **Theorem 1.3 (genuine natural-density form), as a closed term.** -/
theorem theorem13 : Theorem13Genuine :=
  theorem13GenuineFromSyracuse syracuseDensityControl

/-- Strict-bound form of the closed main theorem. -/
theorem theorem13Strict : Theorem13GenuineStrict :=
  theorem13GenuineStrictFromGenuine theorem13

/-- Paper-domain (positive-integer) strict form of the closed main theorem. -/
theorem theorem13PaperDomain : Theorem13GenuinePaperDomain :=
  theorem13GenuinePaperDomainFromStrict theorem13Strict

end TaoCollatzLean