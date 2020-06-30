# Generalised Trigonometric Functions in LEAN

This a summer project as part of the Xena Project's summer project sessions ran in the summer of 2020. That was a lot of summers! I am formalising and placing the generalised trigonometric functions into Lean and proving simple lemmas about them.

## Types of GTF

Firstly we are focussing on two types of GTFs, (1) the wonky square GTFs, which are heavily reliant on |x|^m + |y|^m = 1 and (2) the p-GTFs which are heavily reliant on an integral definition.

## What I want to do
### Wonky Sq
* Define the double angle formulae
* <img src="https://latex.codecogs.com/gif.latex?|sinm(x)|\leq0\text{%20and%20}|cosm(x)|\leq0" /> 
* |sinm x| \leq 0 and |cosm x| \leq 0
* sinm, cosm, secm, cscm periodicity of 2\pi
* tanm, cothm periodicity of \pi
* lim_{x \to 0}{sinm x / x} = 1
* Differentiation?!?

### p-GTF
* Get them to work...

## What I have done
### Wonky Sq
* Defined
* Proved the Zero lemmas

### p-GTF



## Known Issues
* mathlib doesn't have integrals
* 