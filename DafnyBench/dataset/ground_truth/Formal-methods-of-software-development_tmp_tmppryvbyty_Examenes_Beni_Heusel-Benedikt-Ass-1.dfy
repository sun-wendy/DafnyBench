// APELLIDOS: Heusel
// NOMBRE: Benedikt
// ESPECIALIDAD: ninguna (Erasmus)

// ESTÁ PERFECTO, NO HAY NINGUN COMENTARIO MAS ABAJO

// EJERCICIO 1 
// Demostrar el lemma div10_Lemma por inducción en n 
// y luego usarlo para demostrar el lemma div10Forall_Lemma

function exp (x:int,e:nat):int
{
if e == 0 then 1 else x * exp(x,e-1)    
}

lemma div10_Lemma (n:nat)
requires n >= 3;
ensures (exp(3,4*n)+9)%10 == 0
{
   if n == 3 { //paso base
      calc { //sólo para mí, comprobado automaticamente
         (exp(3,4*n)+9);
         (exp(3,4*3)+9);
         exp(3, 12) + 9;
         531441 + 9;
         531450;
         10 * 53145;
      }
   } else { //paso inductivo
         div10_Lemma(n-1);
         //assert (exp(3,4*(n-1))+9)%10 == 0; // HI
         var k := (exp(3,4*(n-1))+9) / 10;
         assert 10 * k == (exp(3,4*(n-1))+9);
         calc {
            exp(3, 4*n) + 9;
            3 * 3 * exp(3,4*n - 2) + 9;
            3 * 3 * 3 * 3 * exp(3,4*n - 4) + 9;
            81 * exp(3,4*n - 4) + 9;
            81 * exp(3,4 * (n-1)) + 9;
            80 * exp(3,4 * (n-1)) + (exp(3,4 * (n-1)) + 9);
            80 * exp(3,4 * (n-1)) + 10*k;
            10 * (8 * exp(3,4 * (n-1)) + k);
         }
   }
}
//Por inducción en n

lemma div10Forall_Lemma ()
ensures forall n :: n>=3 ==> (exp(3,4*n)+9)%10==0
{
   forall n | n>=3 {div10_Lemma(n);}
}
//Llamando al lemma anterior

// EJERCICIO 2
// Demostrar por inducción en n el lemma de abajo acerca de la función sumSerie que se define primero.
// Recuerda que debes JUSTIFICAR como se obtiene la propiedad del ensures a partir de la hipótesis de inducción.

function sumSerie (x:int,n:nat):int
{
if n == 0 then 1 else sumSerie(x,n-1) + exp(x,n)
}

lemma  {:induction false} sumSerie_Lemma (x:int,n:nat)
ensures (1-x) * sumSerie(x,n) == 1 - exp(x,n+1)
{
   if n == 0 { //paso base
      calc { 
         (1-x) * sumSerie(x,n);
         (1-x) * sumSerie(x,0);
         (1-x) * 1;
         1 - x;
         1 - exp(x,1);
         1 - exp(x,n+1);
      }
   } else{ //paso inductivo
      calc {
         (1-x) * sumSerie(x,n);
         (1-x) * (sumSerie(x,n-1) + exp(x,n));
         (1-x) * sumSerie(x,n-1) + (1-x) * exp(x,n);
         {
            sumSerie_Lemma(x, n-1);
            //assert (1-x) * sumSerie(x,n-1) == 1 - exp(x,n); // HI
         }
         1 - exp(x,n) + (1-x) * exp(x,n);
         1 - exp(x,n) + exp(x,n) - x * exp(x,n);
         1 - x * exp(x,n);
         1 - exp(x,n + 1);
      }
   }
}


// EJERCICIO 3 
// Probar el lemma noSq_Lemma por contradicción + casos (ver el esquema de abajo).
// Se niega la propiedad en el ensures y luego se hacen dos casos (1) z%2 == 0 y (2) z%2 == 1.
// En cada uno de los dos casos hay que llegar a probar "assert false"

lemma notSq_Lemma (n:int)
ensures !exists z :: z*z == 4*n + 2
{ //Por contradicción con dos casos:
if exists z :: 	4*n + 2 == z*z 
   {
   var z :| z*z == 4*n + 2 == z*z;
   if z%2 == 0 {
               //llegar aquí a una contradicción y cambiar el "assume false" por "assert false"
            var k := z/2;
            assert z == 2*k;
            calc ==> {
               4*n + 2 == z*z;
               4*n + 2 == (2*k)*(2*k);
               2 * (2*n+1) == 2 * (2*k*k);
               2*n+1 == 2*k*k;
               2*n+1 == 2*(k*k);
            }
            assert 0 == 2*(k*k) % 2 == (2*n+1) % 2 == 1;
            assert false;
   }
   else {
	    //llegar aquí a una contradicción y cambiar el "assume false" por "assert false"
            //assert z % 2 == 1;
            var k := (z-1) / 2;
            assert z == 2*k + 1;
            calc ==> {
               4*n + 2 == z*z;
               4*n + 2 == (2*k + 1)*(2*k + 1);
               4*n + 2 == 4*k*k + 4*k + 1;
               4*n + 2 == 2 * (2*k*k + 2*k) + 1;
               2 * (2*n + 1) == 2 * (2*k*k + 2*k) + 1;
            }
            assert 0 == (2 * (2*n + 1)) % 2 == (2 * (2*k*k + 2*k) + 1) % 2 == 1;
            assert false;
   }      
   }
}



// EJERCICIO 4
//Probar el lemma oneIsEven_Lemma por contradicción, usando también el lemma del EJERCICIO 3.

lemma oneIsEven_Lemma (x:int,y:int,z:int)
requires z*z == x*x + y*y 
ensures x%2 == 0 || y%2 == 0
{
   if !(x%2 == 0 || y%2 == 0) {
      //assert x%2 == 1 && y%2 == 1;
      assert x == 2 * ((x-1)/2) + 1;
      var k: int :| 2*k + 1 == x;
      
      assert y == 2 * ((y-1)/2) + 1;
      var b: int :| 2*b + 1 == y;

      calc {
         x*x + y*y;
         (2*k + 1) * (2*k + 1) + (2*b + 1) * (2*b + 1);
         4*k*k + 4*k + 1 + (2*b + 1) * (2*b + 1);
         4*k*k + 4*k + 1 + 4*b*b + 4*b + 1;
         4*k*k + 4*k + 4*b*b + 4*b + 2;
         4 * (k*k + k + b*b + b) + 2;
      }
      assert z * z == 4 * (k*k + k + b*b + b) + 2;
      notSq_Lemma(k*k + k + b*b + b);
      //assert !exists z :: z*z == 4*(k*k + k + b*b + b) + 2;
      assert false;
   }
}
// Por contradicción, y usando notSq_Lemma.


//////////////////////////////////////////////////////////////////////////////////////////////

/* ESTE EJERCICIO SÓLO DEBES HACERLO SI HAS CONSEGUIDO DEMOSTRAR CON EXITO LOS EJERCICIOS 1 y 2

EJERCICIO 5 
En este ejercicio se dan dos lemma: exp_Lemma y prod_Lemma, que Dafny demuestra automáticamente.
Lo que se pide es probar expPlus1_Lemma, por inducción en n, haciendo una calculation con == y >=,
que en las pistas (hints) use la HI y también llamadas a esos dos lemas.
*/
lemma exp_Lemma(x:int, e:nat)			
requires x >= 1 
ensures exp(x,e) >= 1
{} //NO DEMOSTRAR, USAR PARA PROBAR EL DE ABAJO

lemma prod_Lemma(z:int, a:int, b:int)
requires z >= 1 && a >= b >= 1
ensures  z*a >= z*b
{} //NO DEMOSTRAR, USAR PARA PROBAR EL DE ABAJO

lemma expPlus1_Lemma(x:int,n:nat)
	requires x >= 1 && n >= 1
	ensures exp(x+1,n) >= exp(x,n) + 1 
   {
      if n == 1 {
         calc {
            exp(x+1,n);
            ==
            exp(x+1,1);
            ==
            x + 1;
            >= //efectivamente en el caso base tenemos igualdad
            x + 1;
            ==
            exp(x,1) + 1;
            ==
            exp(x,n) + 1;
         }
      } else {
         calc {
            exp(x+1,n);
            ==
            (x + 1) * exp(x+1,n-1);
            >= {
               expPlus1_Lemma(x, n-1);
               //assert exp(x+1,n-1) >= exp(x,n-1) + 1; HI

               //assert exp(x+1,n-1) >= exp(x,n-1) + 1; // HI
               //aquí se necesitaría tambien prod_lemma,
               //pero parece que el paso se demuestra tambien
               //sin la llamada
            }
            (x + 1) * (exp(x,n-1) + 1);
            ==
            x * exp(x,n-1) + x + exp(x,n-1) + 1;
            ==
            exp(x,n) + x + exp(x,n-1) + 1;
            == 
            exp(x,n) + 1 + exp(x,n-1) + x;
            >= {
               exp_Lemma(x, n-1);
            }
            exp(x,n) + 1;
         }
      }
   }
// Por inducción en n, y usando exp_Lemma y prod_Lemma.
