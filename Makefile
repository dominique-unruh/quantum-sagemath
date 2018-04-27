
SAGEDIR=/opt/SageMath
SAGE=$(SAGEDIR)/sage

install_mosek:
	$(SAGE) -pip install -f https://download.mosek.com/stable/wheel/index.html Mosek

