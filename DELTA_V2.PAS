program row_kwadr;

var
  a,b,c,x,x1,x2,delta:real;

begin;
  writeln('Podaj wartosci wsp. a,b,c');
  readln(a,b,c);
  if (a<0) or (a>0)
               then begin
                      delta:=b*b-4*a*c;
                      writeln('Delta = ',delta);
                      end
               else writeln('To nie jest rownanie kwadratowe !');
  if delta>0
               then begin
                      x1:=(-b+SQRT(delta))/(2*a);
                      x2:=(-b-SQRT(delta))/(2*a);
                      writeln('x1 = ',x1);
                      writeln('x2 = ',x2);
                    end;
  if delta=0
               then begin
                      x:=(-b+SQRT(delta))/(2*a);
                      writeln('x = ',x);
                    end;
  if delta<0
               then
                 writeln('Brak rozwiazan dla podanych parametrow !');
  readln;

end.