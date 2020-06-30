/-
We are going to fiddle with some GTF bits and see if I can make
any leeway through just fiddling
-/

import tactic
import data.real.basic 
import data.complex.exponential

noncomputable theory
open_locale classical
 
open real

notation `|`x`|` := abs x

/- 
We know that the GTFs are defined using two methods, one being 
|x|^p + |y|^q = 1 and an integral, which is a slight mess. The integral is 
probably preferable, but FTC isn't entirely put into mathlib yet. So we are to 
go with the equation version, thing. 
-/

def wonky_square (x y : ℝ) (p q : ℕ) := ∀ p q > 0, |x| ^ p + |y| ^ q = 1

#check wonky_square

/- 
Wonky square now exists, it's an amazing name. So we can go forward and to 
define our GTF's we need to define them as a ratio between the x co-ordinate and
the y co-ordinate. 

How this works is, we take a wonky square of a (p, q) then we go and take a point
that we define using θ and sinₚ(θ) is the y co-ordinate 




Will come bck to wonky square thing, looks slightly confusing for the time
being, new problem. LEAN says no to sin and cos -/

def radius (x : ℝ) (p q : ℕ) := ( |sin x| ^ p + |cos x| ^ q )⁻¹

-- def heavyside (x : ℝ) : ℝ := if x<0 then 0 else 1
-- ^ ignore that, Kevin was trying to teach me something

def sinp (θ : ℝ) (p q : ℕ) := sin θ * radius θ p q 
-- trigonometric sin is defined!!

def cosp (θ : ℝ) (p q : ℕ) := cos θ * radius θ p q
-- So we can onto prove somethings!
-- actually, let us go and define a few more things 

def tanp (θ : ℝ) (p q : ℕ) := sinp θ p q / cosp θ p q

def secp (θ : ℝ) (p q : ℕ) := 1 / cosp θ p q

def cscp (θ : ℝ) (p q : ℕ) := 1 / secp θ p q

-- let us show that these functions follow general trigonometric convention

lemma sinp_zero (p q : ℕ): sinp 0 p q = 0 :=
begin
  unfold sinp,
  rw sin_zero,
  rw zero_mul,
end

-- we know that p q > 0 because the negative values get funny and annoying.

lemma cosp_zero (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0): cosp 0 p q = 1 :=
begin
  unfold cosp,
  unfold radius,
  rw [cos_zero, one_mul, sin_zero, abs_zero, abs_one],
  rw zero_pow',
  norm_num,
  exact hp,
end

lemma tanp_zero (p q : ℕ) : tanp 0 p q = 0 :=
begin 
  unfold tanp,
  rw [sinp_zero, zero_div],
end

lemma secp_zero (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) : secp 0 p q = 1 :=
begin
  unfold secp,
  rw cosp_zero, 
  norm_num,
  exact hp, 
  exact hq,
end

-- We have no πₚ function defined and that's annoying.

