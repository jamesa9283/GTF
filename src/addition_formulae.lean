import tactic
import data.real.basic data.int.basic init.data.int.basic
import data.complex.exponential
import analysis.special_functions.trigonometric data.complex.exponential


-- local imports
 import basic zero_lemmas


/- 031
Let us do the cosₘ x addition formula
-/

-- Thanks, I hate it.
lemma cosm_add ( x y m : ℝ) : cosm (x + y) m = (cosm x m * cosm y m - sinm x m * sinm y m) / (|cosm x m * cosm y m - sinm x m * sinm y m| ^ m + |sinm x m * cosm y m + cosm x m * sinm y m|^m)^ (1/m) :=
begin 
  unfold cosm,
  unfold sinm,
  unfold radius,
  rw [cos_add, sin_add],
  rw sub_mul,
  simp,
  -- nah, this is yuck. I think this is the most cursed thing in lean.
  -- it's worse.
  -- What have I proved: That this definition is just awful.
end

 -- that worked?!? No errors!

/- 032 
Now, for the sinₘ x one!
-/

lemma sinm_add (x y m : ℝ) : sinm (x + y) m = (sinm x m * cosm y m + cosm x m sinm y m)/(|cos x m * cos y m - sin x m * sin y m|^m + |sin x m * cos y m + cos x m * sin y m|^m)^(1/m) :=
begin
  unfold cosm,
  unfold sinm,
  unfold radius,
  rw [cos_add, sin_add],
  rw sub_mul,
  simp,
end