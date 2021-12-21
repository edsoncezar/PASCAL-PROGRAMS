program oceny;
var
  n1,n2:string[20];
  a,b,c,x,y,z:integer;
  s1,s2:real;
begin
  writeln('Podaj nazwisko pierwszego ucznia');
  readln(n1);
  writeln('Podaj oceny');
  readln(a,b,c);
  writeln('Podaj nazwisko drugiego ucznia');
  readln(n2);
  writeln('Podaj oceny');
  readln(x,y,z);
  s1:=(a+b+c)/3;
  s2:=(x+y+z)/3;
  if (s1-s2)>0
  then writeln('Wyzsza srednia ma uczen ',n1);
  if (s1-s2)=0
  then writeln('Srednie sa rowne');
  if (s1-s2)<0
  then writeln('Wyzsza srednia ma uczen ',n2);
  readln;
end.

