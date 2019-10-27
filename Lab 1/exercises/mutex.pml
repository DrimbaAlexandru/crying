bool wantP = false, wantQ = false;

byte nr = 0;

proctype P() 
{    
    printf("Noncritical section P\n");
    atomic 
    {
        !wantQ;
        wantP = true
    }
    printf("Critical section P\n");
    nr = nr + 2;
    wantP = false   
}

proctype Q() 
{
    printf("Noncritical section Q\n");
    atomic 
    {
        !wantP;
        wantQ = true
    }
    printf("Critical section Q\n");
    nr = nr + 1;
    wantQ = false   
}

init 
{
    atomic 
    {
        run P();
        run Q()
    }
    (_nr_pr == 1) -> 
        assert( nr == 3 )
}