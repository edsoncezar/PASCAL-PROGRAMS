program pierwiastek;

var
  x,y:real;

begin;
  write('Podaj liczbe ');
  readln(x);
   if x>=0 then begin
                y:=SQRT(x);
                writeln('Pierwiastek = ',y);
                end
           else writeln('Argument jest ujemny ty nendzna imitacjo KK !!!');
end.