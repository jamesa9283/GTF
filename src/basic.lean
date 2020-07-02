import tactic
import data.real.basic 
import data.complex.exponential analysis.special_functions.pow

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



/-!
## p-GTFs

This is my speciality but it _needs_ integration, so this won't be able to be
filled in until somebody produces some sort of integration in lean or I prove it
out of spite for not having it.
-/
