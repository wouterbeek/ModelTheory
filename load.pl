% The load file for the Model-Theory library.

:- dynamic(user:project/3).
:- multifile(user:project/3).
user:project('ModelTheory', 'Prolog implementation of Model Theory', mt).

:- use_module(load_project).
:- load_project([
  plc-'Prolog-Library-Collection',
  plGraph,
  plSet
]).

