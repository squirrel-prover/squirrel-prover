(*
 * This file is part of the Bisect_ppx Ocamlbuild plugin.
 *
 * This is free and unencumbered software released into the public domain.
 *
 * Anyone is free to copy, modify, publish, use, compile, sell, or
 * distribute this software, either in source code form or as a compiled
 * binary, for any purpose, commercial or non-commercial, and by any
 * means.
 *
 * In jurisdictions that recognize copyright laws, the author or authors
 * of this software dedicate any and all copyright interest in the
 * software to the public domain. We make this dedication for the benefit
 * of the public at large and to the detriment of our heirs and
 * successors. We intend this dedication to be an overt act of
 * relinquishment in perpetuity of all present and future rights to this
 * software under copyright law.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY CLAIM, DAMAGES OR
 * OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
 * ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 *
 * For more information, please refer to <http://unlicense.org/>
 *)

open Ocamlbuild_plugin

let _tag_name = "coverage"
let _environment_variable = "BISECT_COVERAGE"
let _enable = "YES"

let handle_coverage () =
  if getenv ~default:"" _environment_variable <> _enable then
    mark_tag_used _tag_name
  else begin
    flag ["ocaml"; "compile"; _tag_name] (S [A "-package"; A "bisect_ppx"]);
    flag ["ocaml"; "link"; _tag_name] (S [A "-package"; A "bisect_ppx"])
  end

let handle_dispatch = function
  | After_rules -> handle_coverage ()
  | _ -> ()

let () = dispatch handle_dispatch
