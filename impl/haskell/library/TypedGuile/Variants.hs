{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE UnicodeSyntax         #-}

-- | Extensible variants for small-pass compilation.
--   Based on the work in
--   "Variations on Variants", J. Garret Morris
--   <http://homepages.inf.ed.ac.uk/jmorri14/pubs/morris-haskell15-variants.pdf>
module Variants where

data Y
data N

data Fix ε = In (ε (Fix ε))

data (f ⊕ g) ε = InL (f ε) | InR (g ε)

(▽) ∷ (φ1 ε  → α) → (φ2 ε → α) → (φ1 ⊕ φ2) ε → α
(f ▽ _) (InL x) = f x
(_ ▽ g) (InR x) = g x

type family IsIn f g where
  IsIn f f       = Y
  IsIn f (g ⊕ h) = Or (IsIn f g) (IsIn f h)
  IsIn f g       = Y

type family Or b c where
  Or N N = N
  Or b c = Y

data Refl
data L x
data R x

type family Into f g where
  Into f f       = Refl
  Into f (g ⊕ h) = Ifi (Into f g) (IsIn f h)
                       (Into f h) (IsIn f g)
  Into f g       = N

type family Ifi lP inR rP inL where
  Ifi N  inR N  inL = N
  Ifi N  inR rP N   = R rP
  Ifi lP N   rP inL = L lP
  Ifi lP inR rP inL = N

class Inj f g p where
  injP ∷ p → f e → g e

instance Inj f f Refl where
  injP _ = id

instance Inj f g p => Inj f (g ⊕ h) (L p) where
  injP (_ ∷ L p) = InL . injP (undefined ∷ p)

instance Inj f h p => Inj f (g ⊕ h) (R p) where
  injP (_ ∷ R p) = InR . injP (undefined ∷ p)

inj ∷ forall f g e . (Inj f g (Into f g)) => f e → g e
inj = injP (undefined ∷ Into f g)

data OnL (h ∷ * → *)
data OnR (h ∷ * → *)
data Le  (g ∷ * → *) p
data Ri  (f ∷ * → *) p
data Found

type family Minus f g where
  Minus f       f = N
  Minus (f ⊕ g) f = OnL g
  Minus (f ⊕ g) g = OnR f
  Minus (f ⊕ g) h = Ifm g (Minus f h) (IsIn f g) f (Minus g h) (IsIn f h)
  Minus f       g = Found

type family Ifm g lP inR f rP inL where
  Ifm g N  inR f N  inL = N
  Ifm g N  inR f rP N   = OnR f
  Ifm g lP N   f rP inL = OnL g

type family OutOf p where
  OutOf (OnL x)  = x
  OutOf (OnR x)  = x
  OutOf (Le f p) = OutOf p ⊕ f
  OutOf (Ri f p) = f ⊕ OutOf p

type ε1 ⊖ ε2 = Minus ε1 ε2

data CL ε -- lift
data Cλ ε -- lambda
data Cx ε -- product
data Cβ ε -- application
data CN ε -- noop

type α × β = (α, β)

-- Conveniences for writing coproducts of multiple types
type Σ1 ε1          κ = ε1                ⊕ κ
type Σ2 ε1 ε2       κ = ε1 ⊕ ε2           ⊕ κ
type Σ3 ε1 ε2 ε3    κ = ε1 ⊕ ε2 ⊕ ε3      ⊕ κ
type Σ4 ε1 ε2 ε3 ε4 κ = ε1 ⊕ ε2 ⊕ ε3 ⊕ ε4 ⊕ κ

-- Convenience for fixed-point
type FExpr α ε = Expr α (Fix ε)

data Expr α e where
  ELift ∷  α                                     → FExpr α        CL
  ELam  ∷ (FExpr α ε1 → FExpr β ε2)              → FExpr (α → β) (Σ2 ε1 ε2 Cλ)
  ETup  ∷  FExpr α ε1               → FExpr β ε2 → FExpr (α × β) (Σ2 ε1 ε2 Cx)
  EApp  ∷  FExpr (α → β) ε1         → FExpr α ε2 → FExpr β       (Σ2 ε1 ε2 Cβ)
  ENoop ∷  FExpr α ε                             → FExpr α       (ε ⊕ CN)

removeNoop ∷ FExpr α ε → Expr α (ε ⊖ CN)
removeNoop = undefined

main ∷ IO ()
main = return ()
