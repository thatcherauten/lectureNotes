// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

var num: Z = Z.prompt("Enter a number: ")
val numOrig : Z = num


if (num < 0) {
  num = num * -1

  Deduce (
    1 (  ) by 
  )

} else {
  //no code, just for verification

  Deduce (
    1 (  ) by 
  )

}


//How can we assert that num is the absolute value of the input?
//(what was the original input?)

assert(num >= 0)
aseert(num == numOrig | num == numOrig * -1)