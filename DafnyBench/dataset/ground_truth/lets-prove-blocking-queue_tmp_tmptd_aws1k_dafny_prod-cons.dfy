/**
 *  A proof in Dafny of the non blocking property of a queue.
 *  @author Franck Cassez.
 *
 *  @note: based off Modelling Concurrency in Dafny, K.R.M. Leino
 *  @link{http://leino.science/papers/krml260.pdf}
 */
module ProdCons {

    //  A type for process id that supports equality (i.e. p == q is defined).
    type Process(==) 

    //  A type for the elemets in the buffer.
    type T

    /**
     *  The producer/consumer problem.
     *  The set of processes is actuall irrelevant (included here because part of the 
     *  original problem statement ...)
     */
    class ProdCons { 

        /**
         *  Set of processes in the system.
         */
        const P: set<Process>

        /**
         *  The maximal size of the buffer.
         */
        var maxBufferSize : nat 

        /**
         *  The buffer.
         */
        var buffer : seq<T> 

        /**
         *  Invariant.
         *
         *  Buffer should always less than maxBufferSize elements,
         *  Set of processes is not empty
         *  
         */
        predicate valid() 
            reads this
        {
            maxBufferSize > 0 && P != {} &&
            0 <= |buffer| <= maxBufferSize 
        }
        
        /**
         *  Initialise set of processes and buffer and maxBufferSize
         */
        constructor (processes: set<Process>, m: nat ) 
            requires processes != {}        //  Non empty set of processes.
            requires m >= 1                 //  Buffer as at least one cell.
            ensures valid()                 //  After initilisation the invariant is true
        { 
            P := processes;
            buffer := [];
            maxBufferSize := m;
        }

        /**
         *  Enabledness of a put operation.
         *  If enabled any process can perform a put.
         */
        predicate putEnabled(p : Process) 
            reads this
        {
            |buffer| < maxBufferSize
        }

        /** Event: a process puts an element in the queue.  */
        method put(p: Process, t : T) 
            requires valid()                
            requires putEnabled(p)          //  |buffer| < maxBufferSize
            modifies this 
        { 
            buffer := buffer + [t] ;
        }

        /**
         *  Enabledness of a get operation. 
         *  If enabled, any process can perform a get.
         */
        predicate getEnabled(p : Process) 
            reads this
        {
            |buffer| >= 1
        }

        /** Event: a process gets an element from the queue. */
        method get(p: Process) 
            requires getEnabled(p)
            requires valid()                //  Invariant is inductive
            ensures |buffer| == |old(buffer)| - 1   //  this invariant is not needed and can be omitted
            modifies this 
        { 
           //   remove the first element of buffer.
           //   note: Dafny implcitly proves that the tail operation can be performed
           //   as a consequence of  |buffer| >= 1 (getEnabled()). 
           //   To see this, comment out the
           //   requires and an error shows up.
           buffer := buffer[1..];
        }
                
        /** Correctness theorem: no deadlock. 
         *  From any valid state, at least one process is enabled.
         */
        lemma noDeadlock() 
            requires valid() 
            ensures exists p :: p in P && (getEnabled(p) || putEnabled(p))

            //  as processes are irrelevant, this could be simplified
            //  into isBufferNotFull() or isBufferNotEmpty()
        { 
          //    Dafny automatically proves this.  so we can leave the
          //    body of this lemma empty.
          //    But for the sake of clarity, here is the proof.

          //    P is not empty so there is a process p in P
          //    Reads as: select a p of type Process such that p in P
          var p: Process :| p in P ;
          //    Now we have a p.
          //    We are going to use the fact that valid() must hold as it is a pre-condition
            if ( |buffer| > 0 ) {
                assert (getEnabled(p));
            }
            else {
                //  You may comment out the following asserts and Dafny
                //  can figure out the proof from the constraints that are
                //  true in this case.
                //  Becas=use |buffer| == 0 and maxBufferSize >= 1, we can do a put
                assert(|buffer| == 0);
                assert (|buffer| < maxBufferSize); 
                assert(putEnabled(p));
            }
        }
    }
}





