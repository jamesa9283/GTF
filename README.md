# Generalised Trigonometric Functions in LEAN

This a summer project as part of the Xena Project's summer project sessions ran in the summer of 2020. That was a lot of summers! I am formalising and placing the generalised trigonometric functions into Lean and proving simple lemmas about them.

## Types of GTF

Firstly we are focussing on two types of GTFs, (1) the wonky square GTFs, which are heavily reliant on |x|^m + |y|^m = 1 and (2) the p-GTFs which are heavily reliant on an integral definition.

## Numbering System

This is a note on my numbering system. I am proving things in the order that I can work out to prove them. This means the numbering is borked, they are numbers as they are proved.

## What I want to do
### Wonky Sq
*  <img src="https://latex.codecogs.com/gif.latex?\displaystyle{lim_{x\to0}{\text{sin}_m(x)/x}=1}" /> (limit of sin x / x as x tends to 0)
* Differentiability
* Differentials

### p-GTF
* Get them to work...
* Work out how to use FTC in lean.

## Doing
### Wonky Sq
* Continuity

### p-GTFs
* Waiting for Integrals


## What I have done
### Wonky Sq
* Defined
* Proved the Zero lemmas
* sinm, cosm periodicity of <img src="https://latex.codecogs.com/gif.latex?2\pi" />
* Define the double angle formulae
* <img src="https://latex.codecogs.com/gif.latex?|\text{sin}_m(x)|\leq0\text{%20and%20}|\text{cos}_m(x)|\leq0" /> (This was stupid anyways)
* Prove that `tanm x = tan x`

### p-GTF



## Known Issues
* mathlib doesn't have integrals
* 

## References of proof
* Mahdi, Hisham & Elatrash, Mohammed & Elmadhoun, Samar. (2014). On Generalized Trigonometric Functions. Journal of Mathematical Sciences and Applications. 2. 33-38. 10.12691/jmsa-2-3-2. 