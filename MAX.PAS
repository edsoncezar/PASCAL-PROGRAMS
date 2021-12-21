program liczby;
var
  a,b,c,max:real;
begin
  writeln('Podaj 3 liczby');
  readln(a,b,c);
  max:=a;
  if b>max then max:=b;
  if c>max then max:=c;
  writeln('Najwieksza liczba jest : ',max);
end.
