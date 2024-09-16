all: ListUtil.vo FeatureProperties.vo CorrectFindXp.vo EnumXp.vo

CorrectFindXp.vo: ListUtil.vo FeatureProperties.vo

EnumXp.vo: ListUtil.vo FeatureProperties.vo CorrectFindXp.vo

%.vo: %.v
	coqc -Q . EnumXP $<

clean:
	rm -f *.vo *.vok *.vos *.aux *.glob
