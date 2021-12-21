program potega;
var z,n,w:integer;
begin
  writeln('Podaj podstawe i wykladnik');
  readln(z,n);
  w:=1;
  while n>0 do
          begin
            w:=w*z;
            n:=n-1;
          end;
  writeln('Wynik potegowania = ',w);
  readln;
end.
