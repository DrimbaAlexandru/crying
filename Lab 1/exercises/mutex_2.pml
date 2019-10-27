byte semaphore = 1;

byte nr = 0;

#define mutex ( semaphore <= 1 )

proctype P() 
{    
    printf("Noncritical section P\n");
    atomic 
    {
        semaphore > 0;
        semaphore--
    }
    printf("Critical section P\n");
    nr = nr + 2;
    
    semaphore++
}

proctype Q() 
{
    printf("Noncritical section Q\n");
    atomic 
    {
        semaphore > 0;
        semaphore--
    }
    printf("Critical section Q\n");
    nr = nr + 1;
     
    semaphore++
}

init 
{
    atomic 
    {
        run P();
        run Q()
    }
}

ltl { <>( nr == 4 ) } 