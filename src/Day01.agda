module Day01 where

open import IO
open import Function
open import Data.Nat
open import Data.Bool
open import Data.List using (List)
open import Data.Maybe hiding (_>>=_)
open import Data.String
open import Data.Integer hiding (_/ℕ_; _≤ᵇ_; _*_)
open import Data.Product

import Data.Nat as Nat
import Data.Nat.Show as NatShow
import Data.Integer.Show as IntShow
import Data.List as List
import Data.Maybe as Maybe
import Data.String as String
import Data.Integer as Integer

_+ℤ_ : ℤ → ℤ → ℤ
_+ℤ_ = Integer._+_

_+ℕ_ : ℕ → ℕ → ℕ
_+ℕ_ = Nat._+_

_/ℕ_ = Nat._/_

_>ᵇ_ : ℕ → ℕ → Bool
a >ᵇ b = (b ≤ᵇ a) ∧ (not (a ≡ᵇ b))

parseInstruction : String → Maybe ℤ
parseInstruction instr with String.head instr | String.tail instr
... | just 'L' | just x = Maybe.map (-_ ∘ +_) $ NatShow.readMaybe 10 x
... | just 'R' | just x = Maybe.map (+_) $ NatShow.readMaybe 10 x
... | just _ | just _ = nothing
... | just _ | nothing = nothing
... | nothing | _ = nothing

parse : String → List ℤ
parse = List.catMaybes ∘ List.map parseInstruction ∘ lines

runSequence : (ℕ → ℤ → ℕ → ℕ) → List ℤ → ℕ → ℕ
runSequence changeCounter instrs init = proj₂ $ List.foldl move (init ,′ 0) instrs
  where
    move : ℕ × ℕ → ℤ → ℕ × ℕ
    move (current , counter) instr =
      let newpos = instr +ℤ (+ current)
          newposWrapped = newpos %ℕ 100
      in newposWrapped , counter +ℕ (changeCounter current instr newposWrapped)

runSequencePart1 : List ℤ → ℕ → ℕ
runSequencePart1 = runSequence λ { _ _ newpos → if newpos ≡ᵇ 0 then 1 else 0 }

runSequencePart2 : List ℤ → ℕ → ℕ
runSequencePart2 = runSequence changeCounter
  where
    crossed0 : ℕ → ℤ → Bool
    crossed0 0 _ = false
    crossed0 init (+ n) = 100 ≤ᵇ (init +ℕ n)
    crossed0 init n with ((+ init) +ℤ n)
    ... | + 0 = true
    ... | + _ = false
    ... | -[1+ _ ] = true

    changeCounter : ℕ → ℤ → ℕ → ℕ
    changeCounter init instr _ =
      let fullRotations = ((∣ instr ∣) /ℕ 100)
          diff = instr - (sign instr ◃ (fullRotations * 100))
          extra = if (crossed0 init diff) then 1 else 0
      in fullRotations +ℕ extra

main : Main
main = run do
  contents ← readFiniteFile "./inputs/day01.txt"
  let instrs = parse contents
  putStrLn "Part 1:"
  putStrLn ∘ NatShow.show $ runSequencePart1 instrs 50
  putStrLn "Part 2:"
  putStrLn ∘ NatShow.show $ runSequencePart2 instrs 50
