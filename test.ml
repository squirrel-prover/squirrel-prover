(* NOTE: somehow these "open!" are necessary to perform the side effects
 *       in each opened module; we use "open!" instead of "open" to avoid
 *       an "unused open" warning *)

open! Squirrellib.Channel
open! Squirrellib.Process
open! Squirrellib.Term
open! Squirrellib.Constr
open! Squirrellib.Lexer
open! Squirrellib.Completion
open! Squirrellib.Parserbuf
open! Squirrellib.Main

let () = Squirrellib.Checks.run ()
