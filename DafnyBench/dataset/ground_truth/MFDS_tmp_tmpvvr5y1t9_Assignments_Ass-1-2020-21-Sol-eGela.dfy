// Ejercicio 1: Demostrar por inducci�n el siguiente lema:

lemma EcCuadDiv2_Lemma (x:int)
    requires x >= 1 
    ensures (x*x + x) % 2 == 0
{
    if x != 1 { 
        EcCuadDiv2_Lemma(x-1);
        assert x*x+x == ((x-1)*(x-1) + (x-1)) + 2*x;
    }
}


// Ejercicio 2: Demostrar por inducci�n el siguiente lema
// Indicaciones: (1) Puedes llamar al lema del ejercicio anterior, si lo necesitas.
//               (2) Recuerda que, a veces, simplificar la HI puede ayudar a saber donde utilizarla.

lemma EcCubicaDiv6_Lemma (x:int)
    requires x >= 1
    ensures (x*x*x + 3*x*x + 2*x) % 6 == 0
{
    if x>1 {
        EcCubicaDiv6_Lemma(x-1);
        //assert ((x-1)*(x-1)*(x-1) + 3*(x-1)*(x-1) + 2*(x-1)) % 6 == 0; //HI
        assert (x*x*x - 3*x*x + 3*x -1 + 3*x*x - 6*x + 3 + 2*x -2) % 6 == 0; //HI
        assert (x*x*x - x) % 6 == 0; //HI
        assert x*x*x + 3*x*x + 2*x == (x*x*x - x) + 3*(x*x + x);
        EcCuadDiv2_Lemma(x);
    }
}

// Ejercicio 3: Probar por contradicci�n el siguiente lemma:

lemma cubEven_Lemma (x:int)
    requires (x*x*x + 5) % 2 == 1
    ensures x % 2 == 0
{
    if x%2 == 1 {
        var k := (x-1)/2;
        assert x*x*x + 5 == (2*k+1)*(2*k+1)*(2*k+1) + 5
                == 8*k*k*k + 12*k*k + 6*k + 6
                == 2*(4*k*k*k + 6*k*k + 3*k + 3);
        assert false;
    }
}

// Ejercicio 4:  Prueba el siguiente lemma por casos (de acuerdo a los tres valores posibles de x%3)
lemma perfectCube_Lemma (x:int)
    ensures exists z :: (x*x*x == 3*z || x*x*x == 3*z + 1 || x*x*x == 3*z - 1);
{
    if x%3 == 0 {
        var k := x/3;
        assert x*x*x == 27*k*k*k == 3*(9*k*k*k);
    }
    else if x%3 == 1 {
        var k := (x-1)/3;
        assert x*x*x == (3*k+1)*(3*k+1)*(3*k+1) == 27*k*k*k + 27*k*k + 9*k + 1;
        assert x*x*x == 3*(9*k*k*k + 9*k*k + 3*k) + 1;
    }
    else {
        var k := (x-2)/3;
        assert x*x*x == (3*k+2)*(3*k+2)*(3*k+2) == 27*k*k*k + 54*k*k + 36*k + 8;
        assert x*x*x == 3*(9*k*k*k + 18*k*k + 12*k + 3) - 1;
    }
}

// Ejercicio 5: Dada la siguiente funci�n exp y los dos lemmas expGET1_Lemma y prodMon_Lemma (que Dafny demuestra autom�ticamente)
// demostrar el lemma expMon_Lemma por inducci�n en n. Usar calc {} y poner como "hints" las llamadas a los lemmas en los 
// pasos del c�lculo donde son utilizadas.

function exp(x:int, e:nat):int
{
    if e == 0 then 1 else x * exp(x,e-1)
}

lemma expGET1_Lemma(x:int, e:nat)			
    requires x >= 1 
    ensures exp(x,e) >= 1
{}

lemma prodMon_Lemma(z:int, a:int, b:int)
    requires z >= 1 && a >= b >= 1
    ensures  z*a >= z*b
{}

lemma expMon_Lemma(x:int, n:nat)
	requires x >= 1 && n >= 1
	ensures exp(x+1,n) >= exp(x,n) + 1 
{
    if n != 1 { 
        calc {
            exp(x+1,n);
            ==
            (x+1)*exp(x+1,n-1);
            == 
            x*exp(x+1,n-1) + exp(x+1,n-1);
            >= {
                expGET1_Lemma(x+1,n-1);
            }
            x*exp(x+1,n-1);
            >= {
                expMon_Lemma(x,n-1);
                    //assert exp(x+1,n-1) >= (exp(x,n-1) + 1);
                expGET1_Lemma(x+1,n-1);
                    //assert exp(x+1,n-1) >= 1;
                expGET1_Lemma(x,n-1);
                    //assert (exp(x,n-1) + 1) >= 1;
                prodMon_Lemma(x, exp(x+1,n-1), exp(x,n-1) + 1);
                    //assert x*exp(x+1,n-1) >= x*(exp(x,n-1) + 1);
            }
            x*(exp(x,n-1) + 1); 
            ==
            x*exp(x,n-1) + x;
            >=
            exp(x,n)+1;
        }
    }
}

