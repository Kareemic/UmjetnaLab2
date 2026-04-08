import sys
from collections import deque


def parsiraj_klauzulu(linija):
    # iz linije teksta napravi frozenset literala
    linija = linija.strip().lower()
    if not linija or linija.startswith('#'):
        return None
    literali = [l.strip() for l in linija.split(' v ')]
    return frozenset(literali)


def ucitaj_klauzule(putanja):
    # ucitaj klauzule iz datoteke
    klauzule = []
    with open(putanja, 'r', encoding='utf-8') as f:
        for linija in f:
            k = parsiraj_klauzulu(linija)
            if k is not None:
                klauzule.append(k)
    return klauzule


def klauzula_u_str(klauzula):
    # frozenset -> string za ispis
    if not klauzula:
        return "NIL"
    sortirano = sorted(klauzula, key=lambda x: (x.lstrip('~'), x.startswith('~')))
    return ' v '.join(sortirano)


def negiraj_literal(lit):
    # a -> ~a, ~a -> a
    if lit.startswith('~'):
        return lit[1:]
    return '~' + lit


def je_tautologija(klauzula):
    # vraca True ako klauzula sadrzi i literal i njegovu negaciju
    for lit in klauzula:
        if negiraj_literal(lit) in klauzula:
            return True
    return False


def negiraj_klauzulu(klauzula):
    # negacija cilja - svaki literal se negira i postaje zasebna klauzula
    return [frozenset([negiraj_literal(lit)]) for lit in klauzula]


def rezolviraj(k1, k2):
    # rezolucija dviju klauzula, vraca listu novih klauzula
    rezultati = []
    for lit in k1:
        suprotni = negiraj_literal(lit)
        if suprotni in k2:
            nova = (k1 - {lit}) | (k2 - {suprotni})
            if not je_tautologija(nova):
                rezultati.append(nova)
    return rezultati


def rezolucija(premise, cilj):
    cilj_str = klauzula_u_str(cilj)

    # negiraj cilj i dodaj u skup potpore
    negirani_ciljevi = negiraj_klauzulu(cilj)

    # ocisti tautologije
    ciste_premise = [p for p in premise if not je_tautologija(p)]
    cisti_negirani = [nc for nc in negirani_ciljevi if not je_tautologija(nc)]

    # sve klauzule pratimo po indeksu
    svi = {}           # frozenset -> indeks
    po_indeksu = {}    # indeks -> frozenset
    roditelji = {}     # indeks -> (r1, r2) ili None

    br = 1
    for k in ciste_premise:
        if k not in svi:
            svi[k] = br
            po_indeksu[br] = k
            roditelji[br] = None
            br += 1

    # dodaj negirane ciljeve u red za obradu (skup potpore)
    red = deque()
    for k in cisti_negirani:
        if k not in svi:
            svi[k] = br
            po_indeksu[br] = k
            roditelji[br] = None
            red.append(br)
            br += 1
        else:
            red.append(svi[k])

    poznate = set(svi.keys())
    obradeni_parovi = set()
    nil_naden = False
    nil_br = -1

    # glavna petlja - skup potpore strategija
    while red and not nil_naden:
        trenutni = red.popleft()
        trenutna_klauzula = po_indeksu[trenutni]

        for drugi in list(po_indeksu.keys()):
            if nil_naden:
                break
            if drugi == trenutni:
                continue

            par = (min(trenutni, drugi), max(trenutni, drugi))
            if par in obradeni_parovi:
                continue
            obradeni_parovi.add(par)

            for rez in rezolviraj(trenutna_klauzula, po_indeksu[drugi]):
                if len(rez) == 0:
                    # nasli smo NIL!
                    po_indeksu[br] = rez
                    svi[rez] = br
                    roditelji[br] = (min(trenutni, drugi), max(trenutni, drugi))
                    nil_br = br
                    nil_naden = True
                    br += 1
                    break

                if rez in svi:
                    continue
                # provjeri subsumpciju - ako neka poznata klauzula vec pokriva ovu, preskoci
                if any(k <= rez for k in poznate if k != rez):
                    continue

                # makni klauzule koje nova subsumira
                poznate = {k for k in poznate if not (rez < k)}

                svi[rez] = br
                po_indeksu[br] = rez
                roditelji[br] = (min(trenutni, drugi), max(trenutni, drugi))
                poznate.add(rez)
                red.append(br)
                br += 1

    # ispis
    ispis = []

    if nil_naden:
        # idi unatrag od NIL i pokupi sve klauzule na putu
        potrebne = set()
        stog = [nil_br]
        while stog:
            x = stog.pop()
            if x in potrebne:
                continue
            potrebne.add(x)
            if roditelji[x] is not None:
                stog.append(roditelji[x][0])
                stog.append(roditelji[x][1])

        # podijeli na pocetne i izvedene, renumeriraj
        pocetne = sorted(i for i in potrebne if roditelji[i] is None)
        izvedene = sorted(i for i in potrebne if roditelji[i] is not None)
        novi_br = {}
        n = 1
        for i in pocetne:
            novi_br[i] = n
            n += 1
        for i in izvedene:
            novi_br[i] = n
            n += 1

        for i in pocetne:
            ispis.append(f"{novi_br[i]}. {klauzula_u_str(po_indeksu[i])}")
        ispis.append("===============")
        for i in izvedene:
            r1, r2 = roditelji[i]
            ispis.append(f"{novi_br[i]}. {klauzula_u_str(po_indeksu[i])} ({novi_br[r1]}, {novi_br[r2]})")
        ispis.append("===============")
        ispis.append(f"[CONCLUSION]: {cilj_str} is true")
    else:
        n = 1
        for i in sorted(po_indeksu):
            if roditelji.get(i) is None:
                ispis.append(f"{n}. {klauzula_u_str(po_indeksu[i])}")
                n += 1
        ispis.append("===============")
        ispis.append(f"[CONCLUSION]: {cilj_str} is unknown")

    return ispis


def pokreni_rezoluciju(datoteka):
    klauzule = ucitaj_klauzule(datoteka)
    if not klauzule:
        print("[CONCLUSION]: unknown")
        return
    cilj = klauzule[-1]
    premise = klauzule[:-1]
    print('\n'.join(rezolucija(premise, cilj)))


def pokreni_kuhanje(datoteka_klauzula, datoteka_naredbi):
    baza = ucitaj_klauzule(datoteka_klauzula)

    with open(datoteka_naredbi, 'r', encoding='utf-8') as f:
        for linija in f:
            linija = linija.strip()
            if not linija or linija.startswith('#'):
                continue
            linija = linija.lower()

            tekst_klauzule = linija[:-1].strip()
            naredba = linija[-1]
            klauzula = parsiraj_klauzulu(tekst_klauzule)
            if klauzula is None:
                continue

            if naredba == '?':
                print('\n'.join(rezolucija(list(baza), klauzula)))
            elif naredba == '+':
                baza.append(klauzula)
            elif naredba == '-':
                if klauzula in baza:
                    baza.remove(klauzula)


if __name__ == "__main__":
    nacin = sys.argv[1].lower()
    if nacin == "resolution":
        pokreni_rezoluciju(sys.argv[2])
    elif nacin == "cooking":
        pokreni_kuhanje(sys.argv[2], sys.argv[3])
