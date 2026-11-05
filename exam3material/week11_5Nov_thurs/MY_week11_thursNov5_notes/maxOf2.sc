// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._


val a: Z = Z.prompt("Enter first number: ")
val b: Z = Z.prompt("Enter second number: ")

var max: Z = 0

if (a > b) {
  max = a

  Deduce (
    1 ( max == a ) by Premise,
    2 ( a > b ) by Premise,
    3 ( max >= a ) by Algebra*(1),
    4 ( max >= b ) by Algebra*(1, 2)
  )

} else {
  max = b

  Deduce (
    1 ( max == b ) by Premise,
    2 ( !(a > b) ) by Premise,
    3 ( a <= b ) by Algebra*(2),
    4 ( max >= b ) by Algebra*(1),
    5 ( max >= a ) by Algebra*(1, 3) 
  )

}

Deduce (
  1 ( max >= a ) by Premise, 
  2 ( max >= b ) by Premise,
  3 ( max == a | max == b ) by Premise
)

assert(max >= a)
assert(max >= b)
assert(max == a | max == b)


//how can we assert that we've found the max?