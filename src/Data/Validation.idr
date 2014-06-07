module Data.Validation

import Verified

-- the typeclass
class Validate (v : Type -> Type -> Type) where
    total foldValidation : (e -> b) -> (a -> b) -> v e a -> b

-- This is pretty much the Either type

data Validation e a =
        Failure e
    |   Success a

-- Instance Helpers

total
validationMap : (a -> b) -> Validation e a -> Validation e b
validationMap _ (Failure err) = Failure err
validationMap f (Success x)   = Success (f x)


total
validationJoin : Validation e (Validation e a) -> Validation e a
validationJoin (Failure err)            = Failure err
validationJoin (Success (Failure err))  = Failure err
validationJoin (Success (Success x))    = Success x

total
validationBind : (Validation e a) -> (a -> Validation e b) -> Validation e b
validationBind = flip go
    where
        go f = validationJoin . validationMap f

validationLift2 : (a -> b -> c) -> Validation e a -> Validation e b -> Validation e c
validationLift2 f mx my = validationBind mx (\x => validationBind my (\y => Success (f x y)))

validationApply : Validation e (a -> b) -> Validation e a -> Validation e b
validationApply = validationLift2 id

-- Validation Instances

instance Validate Validation where
    foldValidation fail _ (Failure err) = fail err
    foldValidation _ succ (Success x)   = succ x

instance Functor (Validation e) where
    map = validationMap

instance VerifiedFunctor (Validation e) where
    mapIdentity (Failure err) = ?validationMapIdentityFailure
    mapIdentity (Success x)   = ?validationMapIdentitySuccess

    mapComposition (Failure err) f g  = ?validationMapCompositionFailure
    mapComposition (Success x) f g    = ?validationMapCompositionSuccess

instance Applicative (Validation e) where
    pure = Success
    (<$>) = validationApply

instance Monad (Validation e) where
    (>>=) = validationBind



---------- Proofs ----------

Data.Validation.validationMapCompositionSuccess = proof
  intros
  refine refl


Data.Validation.validationMapCompositionFailure = proof
  intros
  refine refl


Data.Validation.validationMapIdentityFailure = proof
  intros
  refine refl


Data.Validation.validationMapIdentitySuccess = proof
  intros
  refine refl


