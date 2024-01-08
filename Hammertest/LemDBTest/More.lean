import Auto.Tactic
import Hammertest.LemDBTest.Base

theorem true_or_false : True ∨ False := Or.inl True.intro

attribute [lemdb zone_defeq] true_or_false
