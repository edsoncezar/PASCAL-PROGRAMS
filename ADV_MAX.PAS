program liczby;
var
  x,max:real;
  m,n,i:integer;
begin
  writeln('Podaj ilosc liczb do porownania');
  readln(n);
  i:=0;
  writeln('Podaj pierwsza liczbe');
  readln(max);
  i:=i+1;
  m:=0;
  m:=i;
  repeat
    writeln('Podaj kolejna liczbe');
    readln(x);
    i:=i+1;
    if x>max
    then begin
           max:=x;
           m:=i;
         end;
  until
    i=n;
  writeln('Najwieksza jest liczba ',max,', ',m,'. z kolei.');
  readln;
end.
