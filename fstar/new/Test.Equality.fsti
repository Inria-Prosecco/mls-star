module Test.Equality

open FStar.All

val test_equality: #a:Type -> a -> a -> ML bool
