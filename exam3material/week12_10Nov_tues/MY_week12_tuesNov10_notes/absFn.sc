// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

def absVal(numOrig: Z) : Z = {
  //what do we need here?
  Contract(
    //no preconditions
    Ensures(Res[Z] >= 0, Res[Z] == numOrig * -1 | Res[Z] == numOrig)
  )

  var num: Z = numOrig

  //update num to be the absolute value of the input
  if (num < 0) {
    num = num * -1

    Deduce(
      1 ( numOrig == Old(num) ) by Premise,
      2 ( Old(num) < 0 ) by Premise,
      3 ( num == Old(num) * -1 ) by Premise,

      4 ( num == numOrig * -1 ) by Algebra*(1, 3),
      5 ( num >= 0 ) by Algebra*(2, 3)

    )
  } else {
    //do nothing -- num is already its own absolute value
    Deduce (
      1 ( !(num < 0) ) by Premise,
      2 ( numOrig == num ) by Premise,
      3 ( num >= 0 ) by Algebra*(1),
      4 ( num == numOrig) by Algebra*(2)
    )
  }

  //what can we say here?
  //what do we need to prove by the end of the function?
  Deduce (
    //need num >= 0;
    1 ( num >= 0 ) by Premise,
    2 ( ( num == numOrig * -1 ) | num == numOrig ) by Premise
  )

  return num

}

////////////////// Test code //////////////

val x: Z = -4

//use function to get absolute value of x
//what *should* the absolute value be?
val answer: Z = absVal(x)

Deduce (
  1 ( x == -4 ) by Premise,
  2 ( answer >= 0 ) by Premise,
  3 ( answer == x * -1 | answer == x ) by Premise,

  4 SubProof (
    5 Assume ( answer == x * -1 ),
    6 ( answer == 4 ) by Algebra*(1, 5)
  )
  7 SubProof (
    8 Assume ( answer == x ) by Premise,
    9 ( F ) by Algebra*(8, 1, 2),
    10 ( answer == 4 ) by BottomE(9)
  )

  11 ( answer == 4 ) by 
)


//what should we be able to assert?
assert(answer == 4)