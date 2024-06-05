method torneo(Valores : array?<real>, i : int, j : int, k : int) returns (pos_padre : int, pos_madre : int)
    requires Valores != null && Valores.Length >= 20 && Valores.Length < 50 && i >= 0 && j >= 0 && k >= 0 
    requires i < Valores.Length && j < Valores.Length && k < Valores.Length && i != j && j != k && k != i 
    ensures exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q // Q

{
    
    assert (Valores[i] < Valores[j] && ((Valores[j] < Valores[k] && exists r | r in {i, j, k} && k != j && j != r && k != r :: Valores[k] >= Valores[j] >= Valores[r]) || (Valores[j] >= Valores[k] && ((Valores[i] < Valores[k] && exists r | r in {i, j, k} && j != k && k != r && j != r :: Valores[j] >= Valores[k] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r | r in {i, j, k} && j != i && i != r && j != r :: Valores[j] >= Valores[i] >= Valores[r]))))) || (Valores[i] >= Valores[j] && ((Valores[j] >= Valores[k] && exists r | r in {i, j, k} && i != j && j != r && i != r :: Valores[i] >= Valores[j] >= Valores[r]) || (Valores[j] < Valores[k] && ((Valores[i] < Valores[k] && exists r | r in {i, j, k} && k != i && i != r && k != r :: Valores[k] >= Valores[i] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r | r in {i, j, k} && i != k && k != r && i != r :: Valores[i] >= Valores[k] >= Valores[r]))))) ; // R : pmd(if..., Q)

        if Valores[i] < Valores[j] {

            assert (Valores[j] < Valores[k] && exists r | r in {i, j, k} && k != j && j != r && k != r :: Valores[k] >= Valores[j] >= Valores[r]) || (Valores[j] >= Valores[k] && ((Valores[i] < Valores[k] && exists r | r in {i, j, k} && j != k && k != r && j != r :: Valores[j] >= Valores[k] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r | r in {i, j, k} && j != i && i != r && j != r :: Valores[j] >= Valores[i] >= Valores[r]))) ; // R1 : pmd(if..., Q)
        
                if Valores[j] < Valores[k] {

                    assert exists r | r in {i, j, k} && k != j && j != r && k != r :: Valores[k] >= Valores[j] >= Valores[r] ; // R11 : pmd(pos_padre := k, R12)

                        pos_padre := k ;
            
                    assert exists p, r | p in {i, j, k} && r in {i, j, k} && p != j && j != r && p != r :: Valores[p] >= Valores[j] >= Valores[r] && pos_padre == p ; // R12 : pmd(pos_madre := j, Q)   

                        pos_madre := j ;

                    assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q ; // Q

                } else {

                    assert (Valores[i] < Valores[k] && exists r | r in {i, j, k} && j != k && k != r && j != r :: Valores[j] >= Valores[k] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r | r in {i, j, k} && j != i && i != r && j != r :: Valores[j] >= Valores[i] >= Valores[r]) ; // R2 : pmd(if..., Q)
            
                        if Valores[i] < Valores[k] {

                            assert exists r | r in {i, j, k} && j != k && k != r && j != r :: Valores[j] >= Valores[k] >= Valores[r] ; // R13 : pmd(pos_padre := j, R14)

                                pos_padre := j ;

                            assert exists p, r | p in {i, j, k} && r in {i, j, k} && p != k && k != r && p != r :: Valores[p] >= Valores[k] >= Valores[r] && pos_padre == p ; // R14 : pmd(pos_madre := k, Q)   

                                pos_madre := k ;

                            assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q ; // Q

                        } else {

                            assert exists r | r in {i, j, k} && j != i && i != r && j != r :: Valores[j] >= Valores[i] >= Valores[r] ; // R15 : pmd(pos_padre := j, R16)

                                pos_padre := j ;

                            assert exists p, r | p in {i, j, k} && r in {i, j, k} && p != i && i != r && p != r :: Valores[p] >= Valores[i] >= Valores[r] && pos_padre == p ; // R16 : pmd(pos_madre := i, Q)   

                                pos_madre := i ;

                            assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q ; // Q

                        }

                }

        } else {

            assert (Valores[j] >= Valores[k] && exists r | r in {i, j, k} && i != j && j != r && i != r :: Valores[i] >= Valores[j] >= Valores[r]) || (Valores[j] < Valores[k] && ((Valores[i] < Valores[k] && exists r | r in {i, j, k} && k != i && i != r && k != r :: Valores[k] >= Valores[i] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r | r in {i, j, k} && i != k && k != r && i != r :: Valores[i] >= Valores[k] >= Valores[r]))) ; // R3 : pmd(if..., Q)

                if Valores[j] >= Valores[k] {
            
                    assert exists r | r in {i, j, k} && i != j && j != r && i != r :: Valores[i] >= Valores[j] >= Valores[r] ; // R17 : pmd(pos_padre := i, R18)  

                        pos_padre := i ;

                    assert exists p, r | p in {i, j, k} && r in {i, j, k} && p != j && j != r && p != r :: Valores[p] >= Valores[j] >= Valores[r] && pos_padre == p ; // R18 : pmd(pos_madre := j, Q)  

                        pos_madre := j ;

                    assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q ; // Q

                } else {

                    assert (Valores[i] < Valores[k] && exists r | r in {i, j, k} && k != i && i != r && k != r :: Valores[k] >= Valores[i] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r | r in {i, j, k} && i != k && k != r && i != r :: Valores[i] >= Valores[k] >= Valores[r]) ; // R4 : pmd(if..., Q)

                        if Valores[i] < Valores[k] {

                            assert exists r | r in {i, j, k} && k != i && i != r && k != r :: Valores[k] >= Valores[i] >= Valores[r] ; // R19 : pmd(pos_padre := k, R110)  

                                pos_padre := k ;

                            assert exists p, r | p in {i, j, k} && r in {i, j, k} && p != i && i != r && p != r :: Valores[p] >= Valores[i] >= Valores[r] && pos_padre == p ; // R110 : pmd(pos_madre := i, Q)  

                                pos_madre := i ;

                            assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q ; // Q

                        } else {

                            assert exists r | r in {i, j, k} && i != k && k != r && i != r :: Valores[i] >= Valores[k] >= Valores[r] ; // R111 : pmd(pos_padre := i, R112)  

                                pos_padre := i ;

                            assert exists p, r | p in {i, j, k} && r in {i, j, k} && p != k && k != r && p != r :: Valores[p] >= Valores[k] >= Valores[r] && pos_padre == p ; // R112 : pmd(pos_madre := k, Q)  

                                pos_madre := k ;

                            assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q ; // Q
           
                        }

                        assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q ; // Q
               
                }

                assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q ; // Q
        
        }

        assert exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q ; // Q

}
