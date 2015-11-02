A verified regular expression matching tool in Idris
===================================

A formalized tool for searching using regular expression. This development is based on the article:

[Regular-expression derivatives reexamined](https://www.mpi-sws.org/~turon/re-deriv.pdf)

by Owens et. al.

Usage
-----

    igrep [REGEXP] [FILE_LIST]

where

- REGEXP: Regular expression to be searched.
- FILE_LIST: List of files to be considered for searching.


Syntax of Regular Expressions
------------------------

The syntax of regular expressions is as follows:

    e ::= e + e
       |    e e
       |    e *
       | ( e )
       | c

where c is some character that isn't +, (,) and *.
Note that some currently the tool does not support operators like
complement, intersection and the empty set.
