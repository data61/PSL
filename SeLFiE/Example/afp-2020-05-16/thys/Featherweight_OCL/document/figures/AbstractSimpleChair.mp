input metafun;
boolean cmykcolors;
cmykcolors := false;
input latexmp;
setupLaTeXMP(
%         preamblefile="preamble"
          class="scrbook"
         ,options="10pt"
         ,fontencoding="T1"
         ,inputencoding="latin1"
         ,packages=("babel[ngerman,USenglish]"
                  &",lmodern,hol-ocl-isar")
       ,preamble=("\renewcommand\familydefault{\ttdefault}")
         ,mode=normal
%        ,multicolor=enable
        );
boolean metauml_defaultLaTeX;
metauml_defaultLaTeX := true;
input metauml;

color MaroonFifty;
MaroonFifty := cmyk(0.00, 0.435, 0.34, 0.16);


beginfig(1)
  

%% Role Hierarchie
AbstractClass.Role("Role")()();
Class.Hearer("Hearer")()();
Class.Speaker("Speaker")()();
Class.Chair("Chair")()();
Class.CoChair("CoCair")()();

topToBottom(30)(Role, Hearer, Speaker); 
topToBottom(30)(CoChair, Chair);
leftToRight(25)(Hearer, CoChair);
drawObjects(Role, Hearer, Speaker);
drawObjects(CoChair, Chair);

link(inheritance)(Hearer.n -- Role.s);
link(inheritance)(Speaker.n -- Hearer.s);
link(inheritance)(CoChair.w -- Hearer.e);
link(inheritance)(Chair.n -- CoChair.s);


Class.Person("Person")("+name:String")();
Class.Participant("Participant")()();
Participant.n = Person.e + (Role.w - Person.e)/2 + (0,-30);
leftToRight(100)(Person, Role);

topToBottom(47)(Person, Session);
Class.Session("Session")("+name:String")
(
%"+invite(p:Person):OclVoid",
 "+findRole(p:Person):Role");
drawObjects(Person, Session,Participant);


% AssocClass
link(association) (Person.e -- Role.w);
item(iAssoc)("person")(obj.sw = Person.e);
item(iAssoc)("0..*")(obj.nw = Person.e);
%
item(iAssoc)("role")(obj.se = Role.w);
item(iAssoc)("0..*")(obj.ne = Role.w);

item(iAssoc)("0..*")(obj.ne = Participant.w);

link(dashedLink)(Participant.n --   (Person.e+(Role.w-Person.e)/2));
path p;
p = fullcircle scaled 6bp shifted (Person.e+(Role.w-Person.e)/2);
fill p withcolor white;
draw p;
%%%

link(association) (pathManhattanX(Participant.w,(Session.n+(-10,0))));
item(iAssoc)("session")(obj.sw = Session.n+(-10,0));
item(iAssoc)("0..1")(obj.se = Session.n+(-10,0));

endfig;

end
