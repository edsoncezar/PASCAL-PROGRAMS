program podzielniki;
var
  x,n,i:longint;
begin
  writeln('Podaj liczbe');
  readln(x);
  n:=x+1;
  i:=0;
  writeln('Liczba ma nastepujace podzielniki : ');
  while n>1 do begin
                 n:=n-1;
                 if (x mod n)=0 then begin
                                       write(n);
                                       write(', ');
                                       i:=i+1;
                                     end;
               end;
  writeln('Ilosc podzielnikow wynosi : ',i);
  readln;
end.
