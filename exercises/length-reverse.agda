open import Data.Nat 
open import Data.Nat.Properties
open import Data.List using (List; []; _∷_; length)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; resp)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

module length-reverse where

private
    rev : {A : Set} → List A → List A → List A
    rev xs [] = xs
    rev xs (y ∷ ys) = rev (y ∷ xs) ys

reverse : {A : Set} → List A → List A
reverse xs = rev [] xs

length-reverse : {A : Set} {xs : List A} → length (reverse xs) ≡ length xs
length-reverse {A} {xs = xs} = length-rev [] xs
    where
    length-rev : (xs ys : List A) → length (rev xs ys) ≡ length (xs) + length (ys)
    length-rev xs [] = sym (+-identityʳ (length xs))
    length-rev xs (y ∷ ys) =
        begin
                length (rev xs (y ∷ ys)) 
            ≡⟨ length-rev  (y ∷ xs) ys ⟩ 
                length (y ∷ xs) + length ys
            ≡⟨ sym (+-suc (length xs) (length ys)) ⟩ 
            length xs + length (y ∷ ys)
            ∎

-- +-suc : suc (x + y) = x + suc y
 