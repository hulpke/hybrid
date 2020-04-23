#Example calculations from the paper

# Heineken Group

F:=FreeGroup("x","y","z");
r:=ParseRelators(F,"[x,[x,y]]=z,[y,[y,z]]=x,[z,[z,x]]=y");;
G:=SimplifiedFpGroup(F/r);;
q:=GQuotients(G,AlternatingGroup(5))[1];
cov:=LiftQuotientHybrid(q,2);;LogInt(Size(Image(cov))/60,2); # returns 5
cov:=LiftQuotientHybrid(cov,2);;LogInt(Size(Image(cov))/60,2); # returns 6
cov:=LiftQuotientHybrid(cov,2);;LogInt(Size(Image(cov))/60,2); # returns 10
cov:=LiftQuotientHybrid(cov,2);;LogInt(Size(Image(cov))/60,2); # returns 14
cov:=LiftQuotientHybrid(cov,2);;LogInt(Size(Image(cov))/60,2); # returns 16
cov:=LiftQuotientHybrid(cov,2);;LogInt(Size(Image(cov))/60,2); # returns 20
cov:=LiftQuotientHybrid(cov,2);;LogInt(Size(Image(cov))/60,2); # returns 24
cov:=LiftQuotientHybrid(cov,2);;LogInt(Size(Image(cov))/60,2); # again 24

# Coxeter (3,4,15;2)

F:=FreeGroup("a","b");
r:=ParseRelators(F,"a3,b4,(ab)15,[a,b]2");
G:=F/r;
q:=GQuotients(G,AlternatingGroup(6))[1];
cov:=LiftQuotientHybrid(q,3);;LogInt(Size(Image(cov))/360,3); # returns 7
cov:=LiftQuotientHybrid(cov,3);;LogInt(Size(Image(cov))/360,3); # returns 15
# the following takes a while 
cov:=LiftQuotientHybrid(cov,3);;LogInt(Size(Image(cov))/360,3); # returns 40

# Coxeter (3,7,15;10)

F:=FreeGroup("a","b");
r:=ParseRelators(F,"a3,b7,(ab)15,[a,b]10");
G:=F/r;
q:=GQuotients(G,AlternatingGroup(10));Length(q); # finds 4
sz:=Factorial(10)/2;

img:=Group(List(GeneratorsOfGroup(G),x->ImagesRepresentative(q[1],x)));;
irr:=IrreducibleModules(img,GF(2));;

cov:=LiftQuotientHybrid(q[1],2:irr:=irr,dims:=[1,8]);;
LogInt(Size(Image(cov))/sz,2); # returns 25

geni:=List(GeneratorsOfGroup(G),x->ImagesRepresentative(cov,x));;
cov:=LiftQuotientHybrid(cov,2:irr:=[geni,irr[2]],dims:=[1,8]);;
LogInt(Size(Image(cov))/sz,2); # returns 30

cov:=LiftQuotientHybrid(q[1],3:dims:=[1..12]);;
LogInt(Size(Image(cov))/sz,3); # returns 19

cov:=LiftQuotientHybrid(q[1],5:dims:=[1..12]);;
LogInt(Size(Image(cov))/sz,5); # returns 8

cov:=LiftQuotientHybrid(q[2],2:dims:=[1,8]);;
LogInt(Size(Image(cov))/sz,2); # returns 8

cov:=LiftQuotientHybrid(q[3],2:dims:=[1,8]);;
LogInt(Size(Image(cov))/sz,2); # returns 9


