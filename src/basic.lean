import tactic
import data.real.basic 
import data.complex.exponential 
import analysis.special_functions.pow

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

/- 001 -/
def wonky_square (x y :ℝ) (m : ℕ) := ∀ m > 0, |x| ^ m + |y| ^ m = 1

-- #check wonky_square

/- 
Wonky square now exists, it's an amazing name. So we can go forward and to 
define our GTF's we need to define them as a ratio between the x co-ordinate and
the y co-ordinate. 

How this works is, we take a wonky square of a m and then we go and take a point
that we define using θ and sinₘ(θ) is the y co-ordinate 

Will come back to wonky square thing, looks slightly confusing for the time
being.  -/

/- 002 -/
def radius (x m : ℝ) := 1 / ( |sin x| ^ m + |cos x| ^ m ) ^ (1/m)

-- def heavyside (x : ℝ) : ℝ := if x<0 then 0 else 1
-- ^ ignore that, Kevin was trying to teach me something

/- 003 -/
def sinm (θ m : ℝ) := sin θ * radius θ m
-- trigonometric sin is defined!!

/- 004 -/
def cosm (θ m : ℝ) := cos θ * radius θ m
-- So we can onto prove somethings!
-- actually, let us go and define a few more things 

/- 005 -/
def tanm (θ m : ℝ) := sinm θ m / cosm θ m

/- 006 -/
def secm (θ m : ℝ) := 1 / cosm θ m

/- 007 -/
def cscm (θ m : ℝ) := 1 / secm θ m

/- 036

-/
lemma sinm_unfolded (x m : ℝ) : sinm x m = sin x / (|cos x| ^ m + |sin x| ^ m) ^ (1 / m) :=
begin
  unfold sinm radius,
  rw [←div_eq_mul_one_div, add_comm],
end

/- 039

-/

lemma cosm_unfolded (x m : ℝ) : cosm x m = cos x / (|cos x| ^ m + |sin x| ^ m) ^ (1 / m) :=
begin
  unfold cosm radius,
  rw [←div_eq_mul_one_div, add_comm],
end


/- 043

-/

lemma exists_cos_pi_half_eq_zero (x m : ℝ) (n : ℤ) : ∃ n, x = (2*n + 1) * pi / 2 → cos x = 0  :=
begin
  use 0,
  intros f,
  rw [mul_zero, zero_add, one_mul] at f,
  rw f,
  simp,
end

/- 042

-/


theorem tanm_eq_tan (x m : ℝ) (n : ℤ) (f : radius x m ≠ 0): tanm x m = tan x :=
begin
  unfold tanm sinm cosm,
  rw tan_eq_sin_div_cos,
  by_cases h : cos x = 0,
  {rw h, simp},
  {rw div_eq_div_iff,
    {ring,},
    {exact mul_ne_zero h f,},
    {exact h}
  },
end

lemma radius_powm (a b c x m : ℝ) (h : m ≠ 0): radius x m ^ m = 1/(|sin x| ^ m + |cos x| ^ m) :=
begin
   unfold radius,
   rw div_rpow,
   rw [one_rpow],
   refine congr rfl _, -- I love this tactic, It's amazing!!
   --rw inv_rpow,
   --rw ←pow_rmul (|sin x| ^ m + |cos x| ^ m) (1 / m) m,
   rw ←rpow_mul,
   rw mul_comm,
   rw ←div_eq_mul_one_div,
   rw div_self,
   rw rpow_one,
   exact h,
   {apply add_nonneg,
  repeat {apply rpow_nonneg_of_nonneg, apply abs_nonneg},},
  {norm_num,},
  {apply rpow_nonneg_of_nonneg,
  apply add_nonneg,
  repeat {apply rpow_nonneg_of_nonneg, apply abs_nonneg},}
end


/-!
## p-GTFs

This is my speciality but it _needs_ integration, so this won't be able to be
filled in until somebody produces some sort of integration in lean or I prove it
out of spite for not having it.
-/
