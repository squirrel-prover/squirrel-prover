type mset.

abstract empty_set : mset.

abstract mem : message -> mset -> bool.

abstract add : message -> mset -> mset.

axiom [any] empty_set_is_empty (x:message) : not (mem x empty_set).
