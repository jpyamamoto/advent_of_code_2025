module Day10 where

open import IO
open import Function
open import Data.Bool using (Bool; if_then_else_; _∧_)
open import Data.Bool.ListAction using (all)
open import Data.Char using (_==_)
open import Data.Fin using (toℕ)
open import Data.List using
  (List; _∷_; []; map; catMaybes; mapMaybe; unsnoc; drop; findIndicesᵇ)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat using (ℕ; suc; zero; _⊓′_)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.Nat.Show using (show; readMaybe)
open import Data.Product using (_,_)
open import Data.String using (String; lines; wordsByᵇ; toList; fromList)

open import Data.Tree.AVL.Sets (<-strictTotalOrder)
  using (⟨Set⟩; delete; insert; member; empty)
  renaming (fromList to setFromList; toList to setToList)

record Machine : Set where
  constructor [_]⟨_⟩
  field
    spec : ⟨Set⟩
    buttons : List (⟨Set⟩ → ⟨Set⟩)

parseSpec : String → ⟨Set⟩
parseSpec = setFromList ∘ map toℕ ∘ findIndicesᵇ ('#' ==_) ∘ drop 1 ∘ toList

init : ∀ {A : Set} → List A → Maybe (List A)
init xs with unsnoc xs
... | just (ys , _) = just ys
... | _ = nothing

toggle : ℕ → ⟨Set⟩ → ⟨Set⟩
toggle x s = if member x s then delete x s else insert x s

wiringToAction : List (Maybe ℕ) → ⟨Set⟩ → ⟨Set⟩
wiringToAction [] s = s
wiringToAction (just x ∷ xs) s = wiringToAction xs (toggle x s)
wiringToAction (nothing ∷ xs) s = wiringToAction xs s

parseButtons : List String → List (⟨Set⟩ → ⟨Set⟩)
parseButtons = map parseButton
  where
    parseButton : String → ⟨Set⟩ → ⟨Set⟩
    parseButton = wiringToAction ∘ map (readMaybe 10) ∘ wordsByᵇ (',' ==_)
                  ∘ fromList ∘ fromMaybe [] ∘ init ∘ drop 1 ∘ toList

parseMachine : String → Maybe Machine
parseMachine s with wordsByᵇ (' ' ==_) s
... | spec ∷ rest with init rest
... | just buttonsStr = just ([ (parseSpec spec) ]⟨ (parseButtons buttonsStr) ⟩)
... | _ = nothing
parseMachine _ | _ = nothing

parse : String → List Machine
parse = catMaybes ∘ map parseMachine ∘ lines

isSubsetOf : ⟨Set⟩ → ⟨Set⟩ → Bool
isSubsetOf s1 s2 = all (λ x → member x s2) (setToList s1)

set≡ : ⟨Set⟩ → ⟨Set⟩ → Bool
set≡ s1 s2 = isSubsetOf s1 s2 ∧ isSubsetOf s2 s1

maybeMin : Maybe ℕ → Maybe ℕ → Maybe ℕ
maybeMin (just x) (just y) = just (x ⊓′ y)
maybeMin (just x) nothing = just x
maybeMin nothing (just x) = just x
maybeMin nothing nothing = nothing

configMachine : List (⟨Set⟩ → ⟨Set⟩) → ℕ → ⟨Set⟩ → ⟨Set⟩ → Maybe ℕ
configMachine [] counter conf spec = if set≡ conf spec then just counter else nothing
configMachine (btn ∷ btns) counter conf spec =
  let try₁ = configMachine btns (suc counter) (btn conf) spec
      try₂ = configMachine btns counter conf spec
  in maybeMin try₁ try₂

part1 : List Machine → ℕ
part1 = sum ∘ mapMaybe λ { [ spec ]⟨ buttons ⟩ → configMachine buttons 0 empty spec }

-- part2 : List Machine → ℕ
-- part2 = ?

main : Main
main = run do
  contents ← readFiniteFile "./inputs/day10.txt"
  let machines = parse contents

  putStrLn "Part 1:"
  putStrLn ∘ show $ part1 machines

  -- putStrLn "Part 2:"
  -- putStrLn ∘ show $ part2 machines
