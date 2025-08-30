import Mathlib

class IsOrderedAlgebra (R A : Type*) [Ring R] [Semiring A] [LinearOrder A] : Prop
    extends IsOrderedRing A

class IsRealClosure (K R : Type*) [Field K] [Field R] [LinearOrder K] [LinearOrder R]
    [IsStrictOrderedRing K] extends IsStrictOrderedRing R, IsOrderedAlgebra K R

theorem test' {S : Type*} [Field S] [LinearOrder S] [IsStrictOrderedRing S]
    (x : S) (hx : IsSquare x) : True := by
  aesop
