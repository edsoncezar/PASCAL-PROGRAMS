program liczby;
var
  a,b,c:real;
begin
  writeln('Podaj 3 liczby');
  readln(a,b,c);
  if(a>b) and (a>c)
  then writeln('Najwieksza jest liczba ',a);
  if(b>c) and (b>a)
  then writeln('Najwieksza jest liczbe ',b);
  if(c>a) and (c>b)
  then writeln('Najwieksza jest liczba ',c);
  readln;
end.