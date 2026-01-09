module Day10 where

open import IO
open import Function
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; not)
open import Data.Bool.ListAction using (all)
open import Data.Char using (_==_)
open import Data.Fin using (toℕ)
open import Data.List using
  (List; _∷_; []; [_]; _++_; map; catMaybes; mapMaybe; unsnoc; drop
  ; findIndicesᵇ; filterᵇ; zip; upTo; length; replicate; zipWith)
open import Data.List.Properties using (≡-dec)
open import Data.List.Relation.Binary.Pointwise.Properties using (decidable)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe) renaming (map to maybeMap)
open import Data.Nat using (ℕ; suc; zero; _≡ᵇ_; _+_; _∸_; _*_; _/_; _%_)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.Properties using (<-strictTotalOrder; ≤-totalOrder; _≟_; _≤?_)
open import Data.Nat.Show using (show; readMaybe)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; lines; wordsByᵇ; toList; fromList)
open import Relation.Nullary.Decidable using (does)

open import Data.List.Extrema ≤-totalOrder using (min)

record Machine : Set where
  constructor _[_]⟨_⟩⟦_⟧
  field
    lights : ℕ
    spec : List ℕ
    buttons : List (List ℕ → List ℕ)
    levels : List ℕ

open Machine

updateAt : ∀ {A : Set} → (xs : List A) → ℕ → (A → A) → List A
updateAt [] _ _ = []
updateAt (x ∷ xs) zero    f = f x ∷ xs
updateAt (x ∷ xs) (suc i) f = x ∷ updateAt xs i f

_[_]%=_ : ∀ {A : Set} → (xs : List A) → ℕ → (A → A) → List A
xs [ i ]%= f = updateAt xs i f

zipWithIndex : {A : Set} → List A → List (ℕ × A)
zipWithIndex xs = zip (upTo (length xs)) xs

init : ∀ {A : Set} → List A → Maybe (List A)
init xs with unsnoc xs
... | just (ys , _) = just ys
... | _ = nothing

wiringToAction : List ℕ → List ℕ → List ℕ
wiringToAction [] xs = xs
wiringToAction (n ∷ ns) xs = (wiringToAction ns xs) [ n ]%= suc

parseSpec : String → ℕ × List ℕ
parseSpec s = let l = drop 1 ∘ toList $ s
                  parseLights = map toℕ ∘ findIndicesᵇ ('#' ==_) 
              in ((length l) ∸ 1) , (parseLights l)

parseButtons : List String → List (List ℕ → List ℕ)
parseButtons = map parseBtn
  where
    parseBtn : String → List ℕ → List ℕ
    parseBtn = wiringToAction ∘ catMaybes ∘ map (readMaybe 10) ∘ wordsByᵇ (',' ==_)
               ∘ fromList ∘ fromMaybe [] ∘ init ∘ drop 1 ∘ toList

parseLevels : String → List ℕ
parseLevels = catMaybes ∘ map (readMaybe 10) ∘ wordsByᵇ (',' ==_)
              ∘ fromList ∘ fromMaybe [] ∘ init ∘ drop 1 ∘ toList

parseMachine : String → Maybe Machine
parseMachine s with wordsByᵇ (' ' ==_) s
... | spec ∷ rest with unsnoc rest
... | just (buttonsStr , levelsStr) with parseSpec spec
... | (n , spec) = just (n [ spec ]⟨ (parseButtons buttonsStr) ⟩⟦ parseLevels levelsStr ⟧)
parseMachine _ | _ | _ = nothing
parseMachine _ | _ = nothing

parse : String → List Machine
parse = catMaybes ∘ map parseMachine ∘ lines

maybeMin : List ℕ → Maybe ℕ
maybeMin [] = nothing
maybeMin (n ∷ ns) = just (min n ns)

subsets : List (List ℕ → List ℕ) → List (ℕ × (List ℕ → List ℕ))
subsets [] = [ 0 , id ]
subsets (btn ∷ btns) = case subsets btns of λ where
  btns′ → btns′ ++ map (λ { (n , b) → suc n , btn ∘ b }) btns′

list≡ : List ℕ → List ℕ → Bool
list≡ xs ys = does (≡-dec _≟_ xs ys)

parity : List ℕ → List ℕ
parity = map toℕ ∘ findIndicesᵇ (not ∘ (0 ≡ᵇ_) ∘ (_% 2))

allLower : List ℕ → List ℕ → Bool
allLower xs ys = does (decidable _≤?_ xs ys)

validButtons : List ℕ → List ℕ → List ℕ → (List ℕ → List ℕ) → Bool
validButtons tmpl tape counters btns with btns tape
... | lights = allLower lights counters ∧ list≡ tmpl (parity lights)

validSeq :
    List ℕ 
  → List ℕ
  → List ℕ
  → List (List ℕ → List ℕ) 
  → List (ℕ × (List ℕ → List ℕ))
validSeq tmpl initial counters =
  filterᵇ (validButtons tmpl initial counters ∘ proj₂) ∘ subsets

decCounts : List ℕ → List ℕ → List ℕ
decCounts xs = map (_/ 2) ∘ zipWith (_∸_) xs

part1 : List Machine → ℕ
part1 = sum ∘ mapMaybe (maybeMin ∘ map proj₁ ∘ getCombos)
  where
    getCombos : Machine → List (ℕ × (List ℕ → List ℕ))
    getCombos (n [ spec ]⟨ buttons ⟩⟦ _ ⟧) =
      validSeq spec (replicate n 0) (replicate n n) buttons

-- This function can be memoized to improve performance.
{-# TERMINATING #-}
goPart2 : ℕ → List (List ℕ → List ℕ) → List ℕ → Maybe ℕ
goPart2 n btns counters with all (0 ≡ᵇ_) counters
... | true = just 0
... | false =
  let doRec (m , btns′) =
        maybeMap ((m +_) ∘ (2 *_))
                 (goPart2 n btns (decCounts counters (btns′ (replicate n 0))))
      validSeqs = validSeq (parity counters) (replicate n 0) counters btns
   in maybeMin ∘ mapMaybe doRec $ validSeqs

part2 : List Machine → ℕ
part2 = sum ∘ mapMaybe go
  where
    go : Machine → Maybe ℕ
    go (n [ _ ]⟨ buttons ⟩⟦ levels ⟧) = goPart2 n buttons levels

main : Main
main = run do
  contents ← readFiniteFile "./inputs/day10.txt"
  let machines = parse contents

  putStrLn "Part 1:"
  putStrLn ∘ show $ part1 machines

  putStrLn "Part 2:"
  putStrLn ∘ show $ part2 machines
