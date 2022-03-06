open import Data.Nat
open import Data.List
import Data.Empty
open import Data.Nat.Properties
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; resp)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Bool
open import Data.Fin hiding (_+_; opposite)
open import Data.Product 

module predavanja3 where

data Tree (A : Set) : Set where
   leaf : Tree A
   node : Tree A → A → Tree A → Tree A 

depth : {A : Set} → Tree A → ℕ
depth leaf = zero
depth (node l n d) = suc (depth l ⊔ depth d)

full : {A : Set} → A → ℕ → Tree A
full x zero = leaf
full x (suc n) = node (full x n) x (full x n)

-- 1. DOKAZI EKVIVALENC
---------------------------------------------------------------------
-- Dokazimo, da je višina drevesa full x n enaka n:
-- MOJ DOKAZ: 

max : (x : ℕ) → x ⊔ x ≡ x
max zero = refl
max (suc x) = cong suc (max x)

depth-full : {A : Set} (x : A) (n : ℕ) → depth ( full x n ) ≡ n
depth-full x zero = refl
depth-full x (suc n) = 
   begin
       depth (full x (suc n))
    ≡⟨ refl ⟩ 
       depth (node (full x n) x (full x n))
    ≡⟨ refl ⟩ 
       suc (depth ((full x n)) ⊔ depth ((full x n)))
    ≡⟨ refl ⟩ 
       suc (depth (full x n)) ⊔ suc (depth (full x n))
    ≡⟨ max (suc (depth (full x n))) ⟩ 
       suc (depth (full x n))
    ≡⟨ cong suc (depth-full x n)  ⟩ 
       suc n
    ∎

-- 2. Dokazimo, da je opposite (xs ++ ys) ≡ opposite ys ++ opposite xs
-- Ta del dokaza je iz interneta:
++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎

-- Kako deluje operator ++ :
-- infixl 5 _++_
-- _++_ : {A : Set} → List A → List A → List A
-- [] ++ ys = ys
-- (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

opposite : {A : Set} → List A → List A
opposite [] = []
opposite (x ∷ xs) = opposite xs ++ (x ∷ [])

-- Dokaz :
opposite-++ : {A : Set} (xs ys : List A) → opposite (xs ++ ys) ≡ opposite ys ++ opposite xs
opposite-++ {A} [] ys = sym (aux1 (opposite ys))
   where
      aux1 : (zs : List A) → zs ++ [] ≡ [] ++ zs
      aux1 [] = refl
      aux1 (x ∷ zs) = cong (x ∷_) (aux1 zs)

opposite-++ {A}  (x ∷ xs) ys =
    begin
        opposite ((x ∷ xs) ++ ys)
      ≡⟨ refl ⟩
        opposite (x ∷ (xs ++ ys))
      ≡⟨ refl ⟩
        opposite (xs ++ ys) ++ (x ∷ [])
      ≡⟨ cong (_++ (x ∷ [])) (opposite-++ xs ys) ⟩
        (opposite ys ++ opposite xs) ++ x ∷ []
      ≡⟨ ++-assoc (opposite ys) (opposite xs) (x ∷ []) ⟩
        opposite ys ++ (opposite xs ++ x ∷ [] )
      ≡⟨ cong (opposite ys ++_) refl ⟩
        opposite ys ++ opposite (x ∷ xs)
    ∎ 

-- 2. Dependent sums
----------------------------------------------------------------------------
Π : (A : Set) → (A → Set) → Set
Π A B = (x : A) → B x
syntax Π A (λ x → B) = Π[ x ∈ A ] B

_∥_ : Set → Set → Bool → Set
(A ∥ B) false = A
(A ∥ B) true = B

ϕ : {A B : Set} → A × B → Π Bool (A ∥ B)
ϕ (x , y) = λ { false → x
              ; true → y }

ψ : {A B : Set} → Π _ (A ∥ B) → A × B
ψ f = (f false) , (f true)

inverse-ψ-ϕ : {A B : Set} (p : A × B) → ψ (ϕ p) ≡ p
inverse-ψ-ϕ (x , y) = refl

postulate funext : {X : Set} {Y : X → Set} (f g : Π[ x ∈ X ] Y x) → ((x : X) → f x ≡ g x) → f ≡ g

inverse-ϕ-ψ : {A B : Set} (f : Π _ (A ∥ B)) → ϕ (ψ f) ≡ f
inverse-ϕ-ψ f = funext (ϕ (ψ f)) f λ { false → refl
                                     ; true → refl }