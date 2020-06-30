import tactic
import data.real.basic 
import data.complex.exponential

noncomputable theory
open_locale classical
 
open real

notation `|`x`|` := abs x

/-!
# General Trigometric Functions

We are going to fiddle with some GTF bits and see if I can makeany leeway through 
just fiddling. We know that the GTFs are defined using two methods, one being 
|x|^m + |y|^m = 1 and an integral, which is a slight mess. The integral is 
probably preferable, but FTC isn't entirely put into mathlib yet. So we are to 
go with the equation version, thing. 


## Wonky Square or m-GTFs
-/

def wonky_square (x y : ℝ) (m : ℕ) := ∀ m > 0, |x| ^ m + |y| ^ m = 1

#check wonky_square

/- 
Wonky square now exists, it's an amazing name. So we can go forward and to 
define our GTF's we need to define them as a ratio between the x co-ordinate and
the y co-ordinate. 

How this works is, we take a wonky square of a m and then we go and take a point
that we define using θ and sinₘ(θ) is the y co-ordinate 

Will come back to wonky square thing, looks slightly confusing for the time
being.  -/

def radius (x : ℝ) (m : ℕ) := 1 / ( |sin x| ^ m + |cos x| ^ m ) ^ (1/m)

-- def heavyside (x : ℝ) : ℝ := if x<0 then 0 else 1
-- ^ ignore that, Kevin was trying to teach me something

def sinm (θ : ℝ) (m : ℕ) := sin θ * radius θ m
-- trigonometric sin is defined!!

def cosm (θ : ℝ) (m : ℕ) := cos θ * radius θ m
-- So we can onto prove somethings!
-- actually, let us go and define a few more things 

def tanm (θ : ℝ) (m : ℕ) := sinm θ m / cosm θ m

def secm (θ : ℝ) (m : ℕ) := 1 / cosm θ m

def cscm (θ : ℝ) (m : ℕ) := 1 / secm θ m

-- let us show that these functions follow general trigonometric convention

lemma sinp_zero (m : ℕ): sinm 0 m = 0 :=
begin
  unfold sinm,
  rw sin_zero,
  rw zero_mul,
end

-- we know that p q > 0 because the negative values get funny and annoying.

lemma cosp_zero (m : ℕ) (hm : m ≠ 0) : cosm 0 m = 1 :=
begin
  unfold cosm,
  unfold radius,
  rw [cos_zero, one_mul, sin_zero, abs_zero, abs_one],
  rw zero_pow',
  norm_num,
  exact hm,
end

lemma tanp_zero (m : ℕ) : tanm 0 m = 0 :=
begin 
  unfold tanm,
  rw [sinp_zero, zero_div],
end

lemma secp_zero (m : ℕ) (hm : m ≠ 0) : secm 0 m = 1 :=
begin
  unfold secm,
  rw cosp_zero, 
  norm_num,
  exact hm,
end


/-!
## p-GTFs

This is my speciality but it _needs_ integration, so this won't be able to be
filled in until somebody produces some sort of integration in lean or I prove it
out of spite for not having it.
-/
