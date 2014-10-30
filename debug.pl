% Loads debug tools for the Model-Theory library.

:- use_module(library(ansi_term)).

% Avoid errors when using gtrace/0 in threads.
:- initialization(guitracer).

:- [load].

