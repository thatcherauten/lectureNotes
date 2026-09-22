// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def imply1(p: B, q: B, r: B): Unit = {
  Deduce(
    (p __>: r, q __>: r ) |- ( p & q __>: r )
      Proof(
      1 (  p __>: r   ) by Premise,
      2 (  q __>: r   ) by Premise,
      
      // need to introduce an implies operator

      3 SubProof (
        // start by assuming the left side of the implies statement
        4 Assume (p & q),

        5 ( p ) by AndE1(4),

        //goal: right side of the implies statement
        6 ( r ) by ImplyE(1, 5),
      ),

      7 (p & q __>: r) by ImplyI(3)


    )
  )
}