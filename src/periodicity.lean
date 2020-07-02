import tactic
import data.real.basic data.int.basic init.data.int.basic
import data.complex.exponential
import analysis.special_functions.trigonometric


-- sinm imports
 import basic zero_lemmas addition_formulae

/-!
Here we are going to prove periodicity lemma's like sinm(2π) = 0 or even 
sinm(x∓π) = -sin(x) and so on. Makng sure we know the periodicity of the 
functions we defined in the previous section.
-/

open real

/- 012
First let us prove that sinm π = 0 
-/
lemma sinm_pi (m : ℝ) : sinm pi m = 0 :=
begin
  unfold sinm,
  rw [sin_pi, zero_mul],
end
 -- We need some half pi lemmas to prove the zero for cosm

/- 013 -/
lemma cos_half_pi : cos (pi/2) = 0 := by simp

/- 014 -/
lemma sin_half_pi : sin (pi/2) = 1 := by simp

/- 015
Now let's prove the cosm_halfpi lemma, it is much the same as the sim_pi above
-/
lemma cosm_halfpi (m : ℝ) (H: m ≠ 0): cosm (pi/2) m = 0 :=
begin
  unfold cosm,
  rw cos_half_pi,
  simp only [zero_mul],
end

/- 016
mathlib doen't seem to have a sin_2pi function so I created it for the next 
 lemma  CORRECTION: I DIDN'T HAVE THE RIGHT IMPORTS
 -/
lemma sin_2pi : sin (2*pi) = 0 :=
begin 
  simp,
end

/- 017
Now for the second case of the cosm, but first let us prove it for cos
-/
lemma cos_3on2pi : cos (3 *pi / 2) = 0 :=
begin
  have H : pi + pi/2 = 3 * pi/2,
  {ring},
  {   rw ←H,
      rw cos_add,
      simp}
end

/- 018
 Now we can prove the above result for our general sine
 -/
lemma sinm_2pi (m : ℝ) : sinm (2 * pi) m = 0 :=
begin
  unfold sinm,
  -- I could at this point use simp, but I thought this was nicer and neater
  rw [sin_2pi, zero_mul],
end

/- 019
 Proving that cosₘ function is zero at 3π/2
-/
lemma cosm_3on2pi (m : ℝ) : cosm (3 * pi / 2) m = 0 :=
begin 
  unfold cosm,
  rw [cos_3on2pi, zero_mul]
end

/- 020
 We are now going to prove that for the naturals that sin(n*π)=0. I am aware this in mathlib
-/
lemma sin_npi_nat (n : ℕ) : sin (n * pi) = 0 :=
begin 
  induction n with d hd,
  { simp },
  { simp only [nat.cast_succ],
    rw [add_mul,sin_add],
    simp [hd] },
end

/- 021
 Now for sinₘ where n is an integer
-/
lemma sinm_npi (m : ℝ) (n : ℤ) : sinm (n * pi) m = 0 :=
begin
  unfold sinm,
  rw [sin_int_mul_pi, zero_mul]
end

/- 022
 I got annoyed that you couldn't just say that (a + b) / c = a/c + b/c so I proved it. 
-/
lemma div_distrib (a b c : ℝ) (c ≠ 0) : (a + b) / c = a/c + b/c :=
begin
  ring,
end

/- 023
 Now to prove that that cos ((2n + 1)π/2) = 0 ∀ n ∈ ℕ
-/
lemma cos_nat_pi_half (n : ℕ) (H : n ≠ 0) : cos ((2 * n + 1) * pi / 2) = 0 :=
begin
  induction n with d hd,
  { simp },
  -- It goes downhill from here!
  { simp only [nat.cast_succ],
    rw [add_mul],
    have H : (2 * (↑d + 1) * pi + 1 * pi) / 2 = (↑d + 1) * pi + pi/2,
    {ring,},
    rw [H, cos_add, cos_half_pi, sin_half_pi, mul_zero],
    norm_num,
    rw add_mul, norm_num,
    rw sin_add, simp only [add_zero, mul_one, sin_pi, cos_pi, mul_neg_eq_neg_mul_symm, neg_eq_zero, mul_zero], -- this is messy and I dislike it
    rw ←sin_nat_mul_pi,
   }
end

/- 024
 Now to prove the above for the integers. It is a lot cleaner.
-/
lemma cos_npi_half (n : ℤ) (H : n ≠ 0) : cos (((2 * n + 1) * pi )/ 2) = 0 :=
begin
  rw add_mul,
  have H : (2 * ↑n * pi + 1 * pi) / 2 = ↑n * pi + pi/2,
    {ring,},
  rw [H, cos_add, cos_half_pi, sin_half_pi, mul_zero, mul_one],
  simp [sin_int_mul_pi],
end

/- 025 
The generalised for, so ∀ n ≠ 0, cosₘ (2n+1)π/2 = 0
-/
lemma cosm_npi_half (n : ℤ) (H : n ≠ 0) (m : ℝ) : cosm ((2 *n + 1) * pi / 2) m = 0 :=
begin
  unfold cosm,
  rw [cos_npi_half n, zero_mul],
  exact H,
end

/- We are now going to prove some things relating to taking a result ±π -/

/- 026 
First up is normal sin! (Again this is probably in mathlib somewhere but I couldn't find it)
-/
lemma sin_selfsim (x : ℝ) : sin(pi - x) = sin(x) :=
begin
  rw sin_sub,
  simp,
end

/- 027
 Now for general cosine (")
-/
lemma cos_selfsim (x : ℝ) : cos (pi - x) = -cos x :=
begin
  rw cos_sub,
  simp,
end

/- 028
 Finally to something interesting! We get to do the generalised sine version of 026
-/

lemma sinm_selfsim (x m : ℝ) : sinm (pi - x) m = sinm x m :=
begin
  unfold sinm,
  rw sin_selfsim,
  unfold radius,
  rw [sin_selfsim, cos_selfsim],
  simp,
end
/- 029
 and the same as 028 but for cosₘ
-/
lemma cosm_selfsim (x m : ℝ) : cosm(pi - x) m = -cosm x m :=
begin 
  unfold cosm,
  rw cos_selfsim,
  unfold radius, 
  rw [sin_selfsim, cos_selfsim],
  simp,
end

-- I may rearrange these wrt whether they are sin, cos, sinₘ, cosₘ etc.

/- 030
Lets now prove that sinₘ (x + π/2) = cosₘ x 
-/
lemma sinm_shift_eq_cosm ( x m : ℝ) : sinm (x + pi/2) m = cosm x m :=
begin
  -- want addition formula first
  rw sinm,
  sorry
end




