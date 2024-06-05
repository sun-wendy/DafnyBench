datatype Valve = ON | OFF

class Pipe{
   var v1: Valve; //outlet valve 
   var v2: Valve; //inlet Valve
   var v3: Valve; //outlet valve
   var in_flowv1: int; //flow in valve v1
   var in_flowv2: int; //flow in vave v2
   var in_flowv3: int; //flow in valve v3

   constructor()
   {
       this.v1:= OFF;
       this.v2:= ON;
   }
  
}
class Tank
{
   var pipe: Pipe;
   var height: int;
    constructor()
    {
        pipe := new Pipe();
    }
} 

method checkRegulation(tank: Tank)
 //requires tank.pipe.v1==OFF && tank.pipe.v2==ON && (tank.pipe.v3==OFF || tank.pipe.v2==ON) 
ensures (tank.height>10 && tank.pipe.v1==OFF && tank.pipe.v3==ON && tank.pipe.v2==old(tank.pipe.v2)) 
|| (tank.height <8 && tank.pipe.v1== OFF && tank.pipe.v2== ON && tank.pipe.v3==old(tank.pipe.v3))
|| ((tank.pipe.in_flowv3 >5 || tank.pipe.in_flowv1 >5 ) && tank.pipe.v2==OFF && tank.pipe.v3==old(tank.pipe.v3) && tank.pipe.v1==old(tank.pipe.v1))
modifies tank.pipe;
 {
    if(tank.height >10)
     {
         tank.pipe.v1:= OFF;
         tank.pipe.v3:= ON;
        assert((tank.height>10 && tank.pipe.v1==OFF && tank.pipe.v3==ON && tank.pipe.v2==old(tank.pipe.v2)));
     }
    else if(tank.height <8)
     {
         
         tank.pipe.v1:= OFF;
         tank.pipe.v2:= ON;
         assert((tank.height <8 && tank.pipe.v1== OFF && tank.pipe.v2== ON && tank.pipe.v3==old(tank.pipe.v3)));
     }
     
     assume(((tank.pipe.in_flowv3 >5 || tank.pipe.in_flowv1 >5 ) && tank.pipe.v2==OFF && tank.pipe.v3==old(tank.pipe.v3) && tank.pipe.v1==old(tank.pipe.v1)));
     /*else if(tank.pipe.in_flowv3 >5 || tank.pipe.in_flowv1> 5)
     {

         tank.pipe.v2:= OFF;
         assume(((tank.pipe.in_flowv3 >5 || tank.pipe.in_flowv1 >5 ) && tank.pipe.v2==OFF && tank.pipe.v3==old(tank.pipe.v3) && tank.pipe.v1==old(tank.pipe.v1)));
     } */
     
 } 
