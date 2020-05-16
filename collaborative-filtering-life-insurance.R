# Collaborative Filtering for Insurance Products: Training #
# Código desarrollado por: J. Fernando Gudiño-Rosero #

# ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ #

# Algorithms used: Association Rules. Random Forests & Neural Networks are used for comparison purposes.
# I build a decision tree incorporating association rules, giving better results
# than the offered by the other models. The reason is the low quality of information due to 
# asymmetric informational problems.

# Descriptive Methodology: Observation of Epanechnikov Distribution Functions.


# ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ #

##  A. BASE DE DATOS DE CLIENTES CON SEGUROS VIGENTES ##

#### I. CARGA DE LIBRERÍAS. ####

library(arules)
library(arulesViz)
library("scatterplot3d")
library("ggplot2")
library(tidyr)
library(purrr)
library(tidyverse)
library(sqldf)
require(sqldf)
library(dplyr)
library(ggplot2)
library(hexbin)
library(openxlsx)
library(ggplot2)
library(reshape2)
library(dplyr)
library(rpart)
library(rpart.plot)
library(caret)
library(ROCR)
require(kernlab)

rm(list=ls())

#### II. DEFINICIÓN DE FUNCIONES Y VARIABLES UTILIZADAS A LO LARGO DEL CÓDIGO ####

distribution_plots <- function(covariate, DataBase, Productos_Insurance){
  total_covariate_insurance <- data.frame(value = numeric(),insurance=character(),stringsAsFactors=FALSE)
  for (p in 1:length(Productos_Insurance)){
    covariate_insurance = DataBase[ DataBase[,Productos_Insurance[p]] == 1,c(covariate,Productos_Insurance[p])]
    colnames(covariate_insurance) = c("value","insurance")
    
    #covariate_insurance[,'value'] <- scale(covariate_insurance[,'value'])
    
    covariate_insurance[,'insurance'] = rep(Productos_Insurance[p],nrow(covariate_insurance))
    total_covariate_insurance = bind_rows(total_covariate_insurance, covariate_insurance)
  }
  total_covariate_insurance = total_covariate_insurance[total_covariate_insurance['value'] != 0,]
  total_covariate_insurance = total_covariate_insurance[!is.na(total_covariate_insurance['value']),]
  total_covariate_insurance['ones'] = as.numeric(rep(1L, nrow(total_covariate_insurance)))
  
  plot = ggplot(total_covariate_insurance,aes(x=value, fill=insurance)) + geom_density(alpha=0.25) + 
    scale_fill_manual( values = c("red","blue",'chocolate1','chartreuse','blueviolet','palegreen','darkgoldenrod1','black'))
  if (covariate == "INGRESO_FINAL"){
    plot = plot + scale_x_continuous(limits = c(0, 4000000))
  } else if (covariate == "VR_PATRIMONIO" | covariate == "VOL_NEG"){
    plot = plot + scale_x_continuous(limits = c(0, 4000000))
  } else{
  }
  
  #ggplot(total_covariate_insurance %>%
  #         group_by(insurance,value)%>% 
  #         summarise (n = n()) %>%
  #         mutate(freq = n / sum(n)),aes(x = value, y = n, fill=insurance)) +
  #  geom_bar(stat="identity",position='dodge')
  
  return(plot)
}

leaf_nodes_filter <- function(db,features_t,intersection,insurance){
  features_list <- matrix(0L,nrow = nrow(db), ncol = length(features_t))
  for (f in 1:length(features_t)){
    features_list[,f] = 1*(db[,features_t[f]])
  }
  if(intersection == "|"){
    feature_vector = rowSums(features_list)} else if (intersection == "&"){
      feature_vector = features_list[,1]*features_list[,2]} else {
        feature_vector = features_list}
  feature_vector[feature_vector > 1] = 1
  
  accuracies <- list()
  successful <- list()
  total <- list()
  
  log_insurance = db[feature_vector == 1 & db[,paste0('EXCEPCIONES_',insurance[1])] == 0,paste0(insurance[1],'_BIN')]
  log_insurance = as.numeric(log_insurance)
  successful [[ insurance[1]  ]] = length(which(log_insurance == 1))
  total [[ insurance[1]  ]] = length(log_insurance)
  accuracies[[ insurance[1]  ]] = (length(which(log_insurance == 1))/length(log_insurance) )*100
  
  if (length(insurance) == 2){
    log_insurance = db[feature_vector == 0 & db[,paste0('EXCEPCIONES_',insurance[2])] == 0,paste0(insurance[2],'_BIN')]
    log_insurance = as.numeric(log_insurance)
    successful [[ insurance[2]  ]] = length(which(log_insurance == 1))
    total [[ insurance[2]  ]] = length(log_insurance)
    accuracies[[ insurance[2]  ]] = (length(which(log_insurance == 1))/length(log_insurance) )*100
  }
  
  return(list(accuracy = accuracies, successful = successful, total = total))
}

root_nodes_filter <- function(db,features_t,intersection,insurance){
  features_list <- matrix(0L,nrow = nrow(db), ncol = length(features_t))
  for (f in 1:length(features_t)){
    features_list[,f] = 1*(db[,features_t[f]])
  }
  if(intersection == "|"){
    feature_vector = rowSums(features_list)} else if (intersection == "&"){
      feature_vector = features_list[,1]*features_list[,2]} else {
        feature_vector = features_list}
  feature_vector[feature_vector > 1] = 1
  log_insurance = db[feature_vector == 1 & db[,paste0('EXCEPCIONES_',insurance)] == 0,paste0(insurance,'_BIN')]
  log_insurance = as.numeric(log_insurance)
  successful = length(which(log_insurance == 1))
  total = length(log_insurance)
  accuracy = successful/total
  db_insurance_new = db[!(feature_vector == 1 & db[,paste0('EXCEPCIONES_',insurance)] == 0),]
  return(list(accuracy = accuracy*100, db = db_insurance_new, successful = successful, total = total))
}

split_nodes_filter <- function(db,features_t,intersection){
  features_list <- matrix(0L,nrow = nrow(db), ncol = length(features_t))
  for (f in 1:length(features_t)){
    features_list[,f] = 1*(db[,features_t[f]])
  }
  if(intersection == "|"){
    feature_vector = rowSums(features_list)} else if (intersection == "&"){
      feature_vector = features_list[,1]*features_list[,2]} else {
        feature_vector = features_list}
  feature_vector[feature_vector > 1] = 1
  db_yes = db[feature_vector == 1,]
  db_no = db[feature_vector == 0,]
  return(list(db_yes = db_yes, db_no = db_no))
}


Categorical_Variables <- c('ACTIVIDAD','COD_OCUPACION','SITUA_VIVIENDA',
                           'SITUACION_LABORAL','ESTADO_CIVIL','DESC_DEPTO','HIPOTECARIO',
                           'LB')

TLMK_Variables <- c('Education_sector','Armed_Forces','Retired','Coastal_reg_retired','Old_threshold','Young_threshold','EDAD')

Branch_Variables <- c('Family_insurance_jobs','Armed_Forces','Retired','VR_PATRIMONIO','INGRESO_FINAL',
                      'EDAD')

# Nombres de seguros libres incluidos #
Productos_Insurance <- c('S1_BIN', 'S3_BIN', 'S5_BIN', 'S7_BIN','S2_BIN','S8_BIN',
                         'S6_BIN','S4_BIN','S9_BIN')
Productos_Insurance_TLMK <- c('S1_BIN', 'S3_BIN','S2_BIN',
                              'S4_BIN')
Productos_Insurance_Branch <- c('S5_BIN', 'S7_BIN','S2_BIN',
                                'S6_BIN')

Excepciones_Variables <- c('EXCEPCIONES_S1','EXCEPCIONES_S3','EXCEPCIONES_S7',
                           'EXCEPCIONES_S2','EXCEPCIONES_S5','EXCEPCIONES_S6',
                           'EXCEPCIONES_S4')

Excepciones_Variables_Branch = c("EXCEPCIONES_S5","EXCEPCIONES_S7","EXCEPCIONES_S2","EXCEPCIONES_S6")
Excepciones_Variables_TLMK = c("EXCEPCIONES_S1","EXCEPCIONES_S3","EXCEPCIONES_S2","EXCEPCIONES_S4")

#### III. LECTURA Y PREPROCESSAMIENTO DE ARCHIVO DE INFORMACIÓN DE CLIENTES CON SEGUROS VIGENTES ####

file = "C:/Users/User/Documents/Collaborative Filtering for Life Insurance/NBO_Insurance_antiguos.xlsx"

# Lectura del archivo de información #

DataBase <- read.xlsx(file, sheet = 1)

# Redefinición de valores missing #

DataBase[is.na(DataBase[,'SITUACION_LABORAL']),'SITUACION_LABORAL'] <- 0
DataBase[is.na(DataBase[,'LB']),'LB'] <- 0
DataBase[is.na(DataBase['SITUA_VIVIENDA']),'SITUA_VIVIENDA'] <- 0
DataBase[is.na(DataBase['ESTADO_CIVIL']),'ESTADO_CIVIL'] <- 0

#### IV. ANÁLISIS DESCRIPTIVO: DISTRIBUCIONES EPANECHNIKOV & ASSOCIATION RULES ########

## (I) Análisis de Distribuciones de Epanechnikov ##

# (i) TLMK: 

# (A) Age (All insurance Products)
# (B) Total Wealth (S4)
# (C) Credit Score (S4)
# (D) Income (S3 and Health are higher than the rest)
# (E) Food Percentage: S4
# (F) Family Expenses Percentage: S4
# (G) Transportation Expenses Percentage: S4


distribution_plots("EDAD", DataBase, c("S1_BIN","S2_BIN","S4_BIN"))
distribution_plots("INGRESO_FINAL", DataBase, Productos_Insurance_TLMK)
distribution_plots("VR_PATRIMONIO", DataBase, Productos_Insurance_TLMK)

# (ii) Office: 
# (A) Age (All insurance Products)
# (B) Total Wealth (S6 & S5)
# (C) Income (All insurance products. S6 income higher than the rest)

distribution_plots("EDAD", DataBase, c("S5_BIN","S7_BIN"))
distribution_plots("INGRESO_FINAL", DataBase, Productos_Insurance_Branch)
distribution_plots("VOL_NEG", DataBase, Productos_Insurance_Branch)


## (II) Análisis de Reglas de Asociación (Association Mining):  ##
# A partir de variables categóricas se detectan reglas de negocio útiles #
# Se transforma la base de datos para implementar el algoritmo A-Priori #

# Filtros preliminares a este análisis #

DataBase[is.na(DataBase[,'COD_OCUPACION']),'COD_OCUPACION'] <- c('ND')
DataBase[,c('COD_OCUPACION')] <- factor(DataBase[,c('COD_OCUPACION')])

DataBase[is.na(DataBase[,'ACTIVIDAD']),'ACTIVIDAD'] <- c('ND')
DataBase[,c('ACTIVIDAD')] <- factor(DataBase[,c('ACTIVIDAD')])

DataBase[is.na(DataBase[,'DESC_DEPTO']),'DESC_DEPTO'] <- c('ND')
DataBase[,c('DESC_DEPTO')] <- factor(DataBase[,c('DESC_DEPTO')])

DataBase[,'LB'] <- as.character(DataBase[,'LB'])
DataBase[DataBase[,'LB'] == '0','LB'] <- c('ND')
DataBase[DataBase[,'LB'] == '1','LB'] <- c('LB')

DataBase[,'HIPOTECARIO'] <- as.character(DataBase[,'HIPOTECARIO'])
DataBase[DataBase[,'HIPOTECARIO'] == '0','HIPOTECARIO'] <- c('ND')
DataBase[DataBase[,'HIPOTECARIO'] == '1','HIPOTECARIO'] <- c('HIPOTECARIO')

DataBase[,'SITUA_VIVIENDA'] <- as.character(DataBase[,'SITUA_VIVIENDA'])
DataBase[DataBase[,'SITUA_VIVIENDA'] == '0','SITUA_VIVIENDA'] <- c('ND')
DataBase[DataBase[,'SITUA_VIVIENDA'] == '1','SITUA_VIVIENDA'] <- c('LIBRE')
DataBase[DataBase[,'SITUA_VIVIENDA'] == '2','SITUA_VIVIENDA'] <- c('HIPOTECADA')
DataBase[DataBase[,'SITUA_VIVIENDA'] == '3','SITUA_VIVIENDA'] <- c('ALQUILER')
DataBase[DataBase[,'SITUA_VIVIENDA'] == '4','SITUA_VIVIENDA'] <- c('FAMILIA')
DataBase[DataBase[,'SITUA_VIVIENDA'] == '5','SITUA_VIVIENDA'] <- c('ND')
DataBase[,c('SITUA_VIVIENDA')] <- factor(DataBase[,c('SITUA_VIVIENDA')])

DataBase[,'SITUACION_LABORAL'] <- as.character(DataBase[,'SITUACION_LABORAL'])
DataBase[DataBase[,'SITUACION_LABORAL'] == '0','SITUACION_LABORAL'] <- c('ND')
DataBase[DataBase[,'SITUACION_LABORAL'] == '1','SITUACION_LABORAL'] <- c('FIJO')
DataBase[DataBase[,'SITUACION_LABORAL'] == '2','SITUACION_LABORAL'] <- c('TEMPORAL')
DataBase[DataBase[,'SITUACION_LABORAL'] == '3','SITUACION_LABORAL'] <- c('AUTONOMO')
DataBase[DataBase[,'SITUACION_LABORAL'] == '4','SITUACION_LABORAL'] <- c('ND')
DataBase[DataBase[,'SITUACION_LABORAL'] == '5','SITUACION_LABORAL'] <- c('ND')
DataBase[,c('SITUACION_LABORAL')] <- factor(DataBase[,c('SITUACION_LABORAL')])

DataBase[,'ESTADO_CIVIL'] <- as.character(DataBase[,'ESTADO_CIVIL'])
DataBase[DataBase[,'ESTADO_CIVIL'] == '0','ESTADO_CIVIL'] <- c('ND')
DataBase[DataBase[,'ESTADO_CIVIL'] == '1','ESTADO_CIVIL'] <- c('SOLTERO')
DataBase[DataBase[,'ESTADO_CIVIL'] == '2','ESTADO_CIVIL'] <- c('CASADO_MANC')
DataBase[DataBase[,'ESTADO_CIVIL'] == '3','ESTADO_CIVIL'] <- c('CASADO_SEP')
DataBase[DataBase[,'ESTADO_CIVIL'] == '4','ESTADO_CIVIL'] <- c('VIUDO')
DataBase[DataBase[,'ESTADO_CIVIL'] == '5','ESTADO_CIVIL'] <- c('SEPARADO')
DataBase[DataBase[,'ESTADO_CIVIL'] == '6','ESTADO_CIVIL'] <- c('DIV')
DataBase[DataBase[,'ESTADO_CIVIL'] == '7','ESTADO_CIVIL'] <- c('UNION_L')
DataBase[,c('ESTADO_CIVIL')] <- factor(DataBase[,c('ESTADO_CIVIL')])
  
DataBase[DataBase[,'S1_BIN'] == 0,'S1_BIN'] <- c('')
DataBase[DataBase[,'S3_BIN'] == 0,'S3_BIN'] <- c('')
DataBase[DataBase[,'S5_BIN'] == 0,'S5_BIN'] <- c('')
DataBase[DataBase[,'S7_BIN'] == 0,'S7_BIN'] <- c('')
DataBase[DataBase[,'S2_BIN'] == 0,'S2_BIN'] <- c('')
DataBase[DataBase[,'S8_BIN'] == 0,'S8_BIN'] <- c('')
DataBase[DataBase[,'S6_BIN'] == 0,'S6_BIN'] <- c('')
DataBase[DataBase[,'S4_BIN'] == 0,'S4_BIN'] <- c('')


DataBase[DataBase[,'S1_BIN'] == 1,'S1_BIN'] <- c('S1')
DataBase[DataBase[,'S3_BIN'] == 1,'S3_BIN'] <- c('S3')
DataBase[DataBase[,'S5_BIN'] == 1,'S5_BIN'] <- c('S5_SC')
DataBase[DataBase[,'S7_BIN'] == 1,'S7_BIN'] <- c('S7')
DataBase[DataBase[,'S2_BIN'] == 1,'S2_BIN'] <- c('S2')
DataBase[DataBase[,'S8_BIN'] == 1,'S8_BIN'] <- c('S8')
DataBase[DataBase[,'S6_BIN'] == 1,'S6_BIN'] <- c('S6')
DataBase[DataBase[,'S4_BIN'] == 1,'S4_BIN'] <- c('S4')

# Cálculo de reglas de asociación #
# Se obtienen reglas de asociación fuertes (reglas de interés) con base en dos requisitos mínimos:
# (i) El número de clientes que cumplen esa regla es mayor a 926 (support = 0.008).
# (ii) El porcentaje mínimo de clientes que tienen el seguro para el cual se está encontrando una regla
# es del 40%, es decir, mínimo 376 clientes (926*40%) de esa regla deben tener ese seguro (confidence = 0.4).

# 1. Reglas de Asociación para el seguro de Accidentes Personales-S1.

S1 <- DataBase[,c('S1_BIN',Categorical_Variables)]
S1[,c('S1_BIN')] <- factor(S1[,c('S1_BIN')])
S1_RULES <- as(S1, "transactions")
summary(S1_RULES)

rules <- apriori(S1_RULES, parameter = list(support = 0.008, confidence = 0.4))
rules

rulesIncomeSmall <- subset(rules, subset = rhs %in% "S1_BIN=S1")
#inspect(rulesIncomeSmall)
inspect(head(rulesIncomeSmall, n = 100, by = "count"))

# Las reglas fuertes encontradas para el seguro S1 son: (2E,EJ,OE)
# (a) Pertenece al sector educativo ó es profesor; (b) Es pensionado/jubilado.
# (c) Vivienda Libre y Nómina.

# 2. Reglas de Asociación para el seguro de S7

S7 <- DataBase[,c('S7_BIN',Categorical_Variables)]
S7[,c('S7_BIN')] <- factor(S7[,c('S7_BIN')])
S7_RULES <- as(S7, "transactions")
summary(S7_RULES)

rules <- apriori(S7_RULES, parameter = list(support = 0.008, confidence = 0.4))
rules

rulesIncomeSmall <- subset(rules, subset = rhs %in% "S7_BIN=S7")
#inspect(rulesIncomeSmall)
inspect(head(rulesIncomeSmall, n = 200, by = "count"))
inspect(head(rulesIncomeSmall, n = 100, by = "confidence"))

# Las reglas fuertes encontradas para el seguro de S7 son:
# (a) Trabaja en el sector salud (Actividad = 2D);
# (b) Trabaja en el sector de construcción y acabados (ACTIVIDAD: 1I).
# (c) Es un profesional con especialización (Código de Ocupación EH).
# (d) Es trabajador independiente (Situación Laboral = Autónomo).
# (e) Trabaja en el sector de servicios & organizaciones sociales (Actividad = 25).
# (f) Trabaja en Administración Pública.
# (g) Es empleado de servicio (EI).
# (h) Es un trabajador temporal.
# (i) Tiene nómina en grandes bancos.
# (j) Unión Libre.
# (k) Tiene crédito hipotecario.

# 3. Reglas de Asociación para el seguro S2

S2 <- DataBase[,c('S2_BIN',Categorical_Variables)]
S2[,c('S2_BIN')] <- factor(S2[,c('S2_BIN')])
S2_RULES <- as(S2, "transactions")
summary(S2_RULES)

rules <- apriori(S2_RULES, parameter = list(support = 0.006, confidence = 0.4))
rules

rulesIncomeSmall <- subset(rules, subset = rhs %in% "S2_BIN=S2")
inspect(head(rulesIncomeSmall, n = 100, by = "count"))

# Las reglas fuertes encontradas para el seguro S2 son:
# (a) Trabaja en las fuerzas armadas (Ocupación EL & Actividad: 23).


# 4. Reglas de Asociación para el seguro S3:

S3 <- DataBase[,c('S3_BIN',Categorical_Variables)]
S3[,c('S3_BIN')] <- factor(S3[,c('S3_BIN')])
S3_RULES <- as(S3, "transactions")
summary(S3_RULES)

rules <- apriori(S3_RULES, parameter = list(support = 0.001, confidence = 0.4))
rules

rulesIncomeSmall <- subset(rules, subset = rhs %in% "S3_BIN=S3")
#inspect(rulesIncomeSmall)
inspect(head(rulesIncomeSmall, n = 100, by = "count"))

# Las reglas fuertes encontradas para el seguro S3 con un support de 0.0005 son:
# (a) Es pensionado y vive en E1,E2,E3 | E4.

# 5. Reglas de Asociación para el seguro S5:

S5 <- DataBase[,c('S5_BIN',Categorical_Variables)]
S5[,c('S5_BIN')] <- factor(S5[,c('S5_BIN')])
S5_RULES <- as(S5, "transactions")
summary(S5_RULES)

rules <- apriori(S5_RULES, parameter = list(support = 0.000025, confidence = 0.4))
rules

rulesIncomeSmall <- subset(rules, subset = rhs %in% "S5_BIN=S5_SC")
#inspect(rulesIncomeSmall)
inspect(head(rulesIncomeSmall, n = 100, by = "count"))
# (a) Pensionado (OE) y vive en E5.

# Todas las anteriores reglas fuertes encontradas se integran dentro del árbol!:

# Se reestablece el tipo de objeto de ciertas variables para seguir utilizado la base con otros propósitos #

DataBase[,c('HIPOTECARIO')] <- (as.numeric(factor(DataBase[,c('HIPOTECARIO')])) ) # 1: Existe
DataBase[,c('LB')] <- (as.numeric(factor(DataBase[,c('LB')])) ) # 2: Existe.

DataBase[DataBase[,'S1_BIN'] == "",'S1_BIN'] <- 0
DataBase[DataBase[,'S3_BIN'] == "",'S3_BIN'] <- 0
DataBase[DataBase[,'S5_BIN'] == "",'S5_BIN'] <- 0
DataBase[DataBase[,'S7_BIN'] == "",'S7_BIN'] <- 0
DataBase[DataBase[,'S2_BIN'] == "",'S2_BIN'] <- 0
DataBase[DataBase[,'S8_BIN'] == "",'S8_BIN'] <- 0
DataBase[DataBase[,'S6_BIN'] == "",'S6_BIN'] <- 0
DataBase[DataBase[,'S4_BIN'] == "",'S4_BIN'] <- 0
DataBase[DataBase[,'S9_BIN'] == "",'S9_BIN'] <- 0

DataBase[DataBase[,'S1_BIN'] == 'S1','S1_BIN'] <- 1
DataBase[DataBase[,'S3_BIN'] == 'S3','S3_BIN'] <- 1
DataBase[DataBase[,'S5_BIN'] == 'S5_SC','S5_BIN'] <- 1
DataBase[DataBase[,'S7_BIN'] == 'S7','S7_BIN'] <- 1
DataBase[DataBase[,'S2_BIN'] == 'S2','S2_BIN'] <- 1
DataBase[DataBase[,'S8_BIN'] == 'S8','S8_BIN'] <- 1
DataBase[DataBase[,'S6_BIN'] == 'S6','S6_BIN'] <- 1
DataBase[DataBase[,'S4_BIN'] == 'S4','S4_BIN'] <- 1
DataBase[DataBase[,'S9_BIN'] == 'S9','S9_BIN'] <- 1


Health_split_db <- Health_split_db[(DataBase[,c("S1_BIN")] == 0 & DataBase[,c("S3_BIN")] == 1 & DataBase[,c("EXCEPCIONES_S3")] == 0) | (DataBase[,c("S1_BIN")] == 1 & DataBase[,c("S3_BIN")] == 0 & DataBase[,c("EXCEPCIONES_S1")] == 0),]
S3 <- Health_split_db[,c('S3_BIN',Categorical_Variables)]
S3[,c('S3_BIN')] <- factor(S3[,c('S3_BIN')])
S3_RULES <- as(S3, "transactions")
summary(S3_RULES)
rules <- apriori(S3_RULES, parameter = list(support = 0.0005, confidence = 0.4))
rules
rulesIncomeSmall <- subset(rules, subset = rhs %in% "S3_BIN=1")
inspect(head(rulesIncomeSmall, n = 100, by = "count"))
# No hay reglas fuertes significativas.

#### V. DERIVACIÓN DE ÁRBOL DE DECISIÓN Y OPTIMIZACIÓN DE MACHINE LEARNING ####

# (i) TLMK: 

TLMK_db <- DataBase[rowSums(sapply(DataBase[,Productos_Insurance_TLMK], as.numeric))>0,]

TLMK_db[,"Armed_Forces"] = 1*((TLMK_db['ACTIVIDAD'] == '23' | TLMK_db['COD_OCUPACION'] == 'EL') & (TLMK_db['TOTAL_OFICINA'] <= 2)  )
TLMK_db[,"Education_sector"] = 1*(TLMK_db['ACTIVIDAD'] == '2E' | TLMK_db['COD_OCUPACION'] == 'EJ')
TLMK_db[,"Retired"] = 1*(TLMK_db['COD_OCUPACION'] == 'OE' | TLMK_db['PENSIONADO'] == 1) 
TLMK_db[,"Coastal_reg_retired"] = 1*((TLMK_db['DESC_DEPTO'] == 'E1' | TLMK_db['DESC_DEPTO'] == 'E2' | TLMK_db['DESC_DEPTO'] == 'E3' | TLMK_db['DESC_DEPTO'] == 'E4' ) ) 
TLMK_db[,"Old_threshold"] = 1*(TLMK_db['EDAD'] >= 41)
TLMK_db[,"Young_threshold"] = 1*(TLMK_db['EDAD'] > 28)

# TLMK - Decision Tree!:

r <- root_nodes_filter(TLMK_db,c('Education_sector'),'','S1') #81.6% de la muestra total. 24.02% del total posible (6255/26032).
f_1 <- root_nodes_filter(r$db,c('Armed_Forces'),'','S2') # 67.5% de la muestra total. 22.66% del total posible (3648/13730).
s_2 <- split_nodes_filter(f_1$db,c('Retired'),'')
f_4 <- leaf_nodes_filter(s_2$db_yes,c('Coastal_reg_retired'),'',c('S3','S1')) # 47.2% & 80.1% de la muestra total. 2.5% y 14% del total posible (233/9349, 3646/26032).
f_6 <- root_nodes_filter(s_2$db_no,c('Old_threshold'),'',('S1')) #77%. 30.24% del total posible (7874/26032).
s_3 <- leaf_nodes_filter(f_6$db,c('Young_threshold'),'',c('S4','S2')) # 

# S1: 68.28%.
# S3: 2.5%.
# S2: 68.57%.
# S4: 30.59%.

TLMK_db[,Productos_Insurance_TLMK] = sapply(TLMK_db[,Productos_Insurance_TLMK],as.numeric)*abs(TLMK_db[,Excepciones_Variables_TLMK]-1)

total_covariate_insurance <- data.frame(Education_sector = numeric(), Armed_Forces = numeric(),
                                        Retired = numeric(), Coastal_reg_retired = numeric(),
                                        Old_threshold = numeric(), Young_threshold = numeric(),
                                        EDAD = numeric(), insurance=character(),stringsAsFactors=FALSE)
for (p in 1:length(Productos_Insurance_TLMK)){
  covariate_insurance = TLMK_db[TLMK_db[,Productos_Insurance_TLMK[p]] == 1,c(TLMK_Variables,Productos_Insurance_TLMK[p])]
  colnames(covariate_insurance) = c(TLMK_Variables,"insurance")
  
  covariate_insurance[,'insurance'] = rep(Productos_Insurance_TLMK[p],nrow(covariate_insurance))
  total_covariate_insurance = bind_rows(total_covariate_insurance, covariate_insurance)
}
total_covariate_insurance[,"EDAD"] <- scale(total_covariate_insurance[,"EDAD"])
head(total_covariate_insurance)


grid.rf <- expand.grid(mtry=2:7) # Default is "ceiling(sqrt(nvar))"
results.rf.opt <- caret::train(insurance ~ Education_sector + Armed_Forces + Retired
                               + Coastal_reg_retired + EDAD, 
                               data = total_covariate_insurance,
                               method = "rf",
                               tuneGrid = grid.rf,
                               metric = "ROC",
                               trControl=trainControl(method = "cv", sampling="up", classProbs = TRUE))


rf <- predict(object=results.rf.opt, newdata=total_covariate_insurance, type = "raw")

confusionMatrix(data = as.factor(1*(rf == 'S1_BIN')), reference = as.factor(1*(total_covariate_insurance[,"insurance"] == 'S1_BIN')), positive = '1')
confusionMatrix(data = as.factor(1*(rf == 'S2_BIN')), reference = as.factor(1*(total_covariate_insurance[,"insurance"] == 'S2_BIN')), positive = '1')
confusionMatrix(data = as.factor(1*(rf == 'S3_BIN')), reference = as.factor(1*(total_covariate_insurance[,"insurance"] == 'S3_BIN')), positive = '1')
confusionMatrix(data = as.factor(1*(rf == 'S4_BIN')), reference = as.factor(1*(total_covariate_insurance[,"insurance"] == 'S4_BIN')), positive = '1')


# S1: 21281/26032 = 81.74%
# S3: 444/9349 = 4.74%
# S2: 11483/13730 = 83.63%
# S4: 0%.

grid.nn <- expand.grid(size = seq(from = 1, to = 10, by = 1),
                       decay = 0)
results.nn.opt <- caret::train(insurance ~ Education_sector + Armed_Forces + Retired
                               + Coastal_reg_retired + EDAD, 
                               data = total_covariate_insurance, 
                               tuneGrid = grid.nn,
                               metric = "ROC",
                               method = "nnet",
                               trControl=trainControl(method = "cv", sampling="up",classProbs = TRUE))

nn <- predict(object=results.nn.opt, newdata=total_covariate_insurance, type = "raw")

confusionMatrix(data = as.factor(1*(nn == 'S1_BIN')), reference = as.factor(1*(total_covariate_insurance[,"insurance"] == 'S1_BIN')), positive = '1')
confusionMatrix(data = as.factor(1*(nn == 'S2_BIN')), reference = as.factor(1*(total_covariate_insurance[,"insurance"] == 'S2_BIN')), positive = '1')
confusionMatrix(data = as.factor(1*(nn == 'S3_BIN')), reference = as.factor(1*(total_covariate_insurance[,"insurance"] == 'S3_BIN')), positive = '1')
confusionMatrix(data = as.factor(1*(nn == 'S4_BIN')), reference = as.factor(1*(total_covariate_insurance[,"insurance"] == 'S4_BIN')), positive = '1')

# S1: 22370/26032 = 85.93%
# S2: 10358/13730 = 75.44%
# S3: 436/9349 = 4.66%
# S4: 0 = 0%


##

# (ii) Commercial Branches: 

Branch_db <- DataBase[rowSums(sapply(DataBase[,Productos_Insurance_Branch], as.numeric))>0,]

Branch_db[,"Armed_Forces"] = 1*((Branch_db[,'ACTIVIDAD'] == '23' | Branch_db[,'COD_OCUPACION'] == 'EL') & (Branch_db[,"TOTAL_OFICINA"]> 2))
Branch_db[,"SALUD_JOB"] = 1*(Branch_db[,'ACTIVIDAD'] == '2D')
Branch_db[,"CONSTRUCCION_JOB"] = 1*(Branch_db[,'ACTIVIDAD'] == '1I')
Branch_db[,"ORG_SOCIAL_JOB"] = 1*(Branch_db[,'ACTIVIDAD'] == '25')
Branch_db[,"PROFESIONAL_ESP"] = 1*(Branch_db[,'COD_OCUPACION'] == 'EH')
Branch_db[,"EMPLEADO_S"] = 1*(Branch_db[,'COD_OCUPACION'] == 'EI')
Branch_db[,"HIPOTECARIO"] = 1*(Branch_db[,'HIPOTECARIO'] == 1)
Branch_db[,"NO_LB"] = 1*(Branch_db[,'LB'] == 1)
Branch_db[,"UNION_LIBRE"] = 1*(Branch_db[,'ESTADO_CIVIL'] == 'UNION_L')
Branch_db[,"TEMPORAL_JOB"] = 1*(Branch_db[,'SITUACION_LABORAL'] == 'TEMPORAL')
Branch_db[,"ADMON_PUBLICA_JOB"] = 1*(Branch_db[,'ACTIVIDAD'] == '2A')
Branch_db[,"PENSIONADO_E5"] = 1*(Branch_db[,'COD_OCUPACION'] == 'OE')*(1*(Branch_db[,'DESC_DEPTO'] == 'E5'))
Branch_db[,"Family_insurance_jobs"] = Branch_db[,"SALUD_JOB"] + Branch_db[,"CONSTRUCCION_JOB"] + Branch_db[,"ORG_SOCIAL_JOB"] + Branch_db[,"PROFESIONAL_ESP"] + 
  Branch_db[,"ADMON_PUBLICA_JOB"] + Branch_db[,"NO_LB"] + Branch_db[,"HIPOTECARIO"] + Branch_db[,"UNION_LIBRE"] + Branch_db[,"TEMPORAL_JOB"] #+ Branch_db[,"EMPLEADO_S"] 

Branch_db[,"Retired"] = 1*(Branch_db[,'COD_OCUPACION'] == 'OE' | Branch_db[,'PENSIONADO'] == 1) 
Branch_db[,"Old_threshold"] = 1*(Branch_db[,'EDAD'] > 55)
Branch_db[,"Wealth_threshold"] = 1*(Branch_db[,'VOL_NEG'] > 2000000)
Branch_db[,"Income_threshold"] = 1*(Branch_db[,'INGRESO_FINAL'] > 2500000)

#
DataBase[,"AAFF"] = 1*(DataBase['ACTIVIDAD'] == '23' | DataBase['COD_OCUPACION'] == 'EL')
AAFF_db = DataBase[DataBase[,"AAFF"] == 1,]
table(AAFF_db[,"TOTAL_OFICINA"])
median(AAFF_db[AAFF_db[,"TOTAL_OFICINA"]>0,"TOTAL_OFICINA"])


## Branch Decision Tree:

r <- root_nodes_filter(Branch_db,c('Retired'),'','S5') #66.7% de la muestra total. 49.70% del total posible (4614/9283).
s_3 <- root_nodes_filter(r$db,c('Wealth_threshold','Income_threshold'),'&','S6') # 2.21% de la muestra total. 58.02% del total posible (170/293).
f_1 <- root_nodes_filter(s_3$db,c('Family_insurance_jobs'),'','S7') # 71.2% de la muestra total. 35.61% del total posible (10767/30229).
s_2 <- root_nodes_filter(f_1$db,c('Armed_Forces'),'','S2') # 70.5% de la muestra total. 21.47% del total posible (508/2366).
s_4 <- leaf_nodes_filter(s_2$db,c('Old_threshold'),'',c('S5','S7')) # 53.7% & 56.9% de la muestra total.5.12% & 39.31% del total posible (476/9283 & 11886/30229).

# S5: 49.7 + 3.88  = 53.58%
# S2:  = 29.58%
# S6: 69.62% 
# S7: 53.70%.

Branch_db[,Productos_Insurance_Branch] = sapply(Branch_db[,Productos_Insurance_Branch],as.numeric)*abs(Branch_db[,Excepciones_Variables_Branch]-1)

total_covariate_insurance <- data.frame(Family_insurance_jobs = numeric(), Armed_Forces = numeric(),
                                        Retired = numeric(), VR_PATRIMONIO = numeric(), INGRESO_FINAL = numeric(),
                                        EDAD = numeric(), insurance=character(),stringsAsFactors=FALSE)
for (p in 1:length(Productos_Insurance_Branch)){
  covariate_insurance = Branch_db[Branch_db[,Productos_Insurance_Branch[p]] == 1,c(Branch_Variables,Productos_Insurance_Branch[p])]
  colnames(covariate_insurance) = c(Branch_Variables,"insurance")
  
  covariate_insurance[,'insurance'] = rep(Productos_Insurance_Branch[p],nrow(covariate_insurance))
  total_covariate_insurance = bind_rows(total_covariate_insurance, covariate_insurance)
}
total_covariate_insurance <- total_covariate_insurance[complete.cases(total_covariate_insurance),]
total_covariate_insurance[,c('VR_PATRIMONIO','INGRESO_FINAL','EDAD')] <- scale(total_covariate_insurance[,c('VR_PATRIMONIO','INGRESO_FINAL','EDAD')])

head(total_covariate_insurance)

grid.nn <- expand.grid(size = seq(from = 1, to = 10, by = 1),
                       decay = 0)
results.nn.opt <- caret::train(insurance ~ Family_insurance_jobs + Armed_Forces + Retired
                               + VR_PATRIMONIO + INGRESO_FINAL + EDAD, 
                               data = total_covariate_insurance, 
                               tuneGrid = grid.nn,
                               metric = "Accuracy",
                               method = "nnet",
                               trControl=trainControl(method = "cv"))

nn <- predict(object=results.nn.opt, newdata=total_covariate_insurance, type = "raw")

confusionMatrix(data = as.factor(1*(nn == 'S5_BIN')), reference = as.factor(1*(total_covariate_insurance[,"insurance"] == 'S5_BIN')), positive = '1')
confusionMatrix(data = as.factor(1*(nn == 'S7_BIN')), reference = as.factor(1*(total_covariate_insurance[,"insurance"] == 'S7_BIN')), positive = '1')
confusionMatrix(data = as.factor(1*(nn == 'S6_BIN')), reference = as.factor(1*(total_covariate_insurance[,"insurance"] == 'S6_BIN')), positive = '1')
confusionMatrix(data = as.factor(1*(nn == 'S2_BIN')), reference = as.factor(1*(total_covariate_insurance[,"insurance"] == 'S2_BIN')), positive = '1')


grid.rf <- expand.grid(mtry=2:6) # Default is "ceiling(sqrt(nvar))"
results.rf.opt <- caret::train(insurance ~ Family_insurance_jobs + Armed_Forces + Retired
                               + VR_PATRIMONIO + INGRESO_FINAL + EDAD, 
                               data = total_covariate_insurance,
                               method = "rf",
                               tuneGrid = grid.rf,
                               metric = "Accuracy",
                               trControl=trainControl(method = "cv"))


rf <- predict(object=results.rf.opt, newdata=total_covariate_insurance, type = "raw")

confusionMatrix(data = as.factor(1*(rf == 'S5_BIN')), reference = as.factor(1*(total_covariate_insurance[,"insurance"] == 'S5_BIN')), positive = '1')
confusionMatrix(data = as.factor(1*(rf == 'S7_BIN')), reference = as.factor(1*(total_covariate_insurance[,"insurance"] == 'S7_BIN')), positive = '1')
confusionMatrix(data = as.factor(1*(rf == 'S6_BIN')), reference = as.factor(1*(total_covariate_insurance[,"insurance"] == 'S6_BIN')), positive = '1')
confusionMatrix(data = as.factor(1*(rf == 'S2_BIN')), reference = as.factor(1*(total_covariate_insurance[,"insurance"] == 'S2_BIN')), positive = '1')


colSums(sapply(Branch_db[,Productos_Insurance_Branch], as.numeric))
# S5: 2590/9283 = 27.90%
# S7: 15199/34098 = 44.57%
# S6: 0/375 = 0%
# S2: 3730/(16290-X) = 22.89%

rf_prob <- predict(object=results.rf.opt, newdata=total_covariate_insurance, type = "prob")

ggplot(rf_prob,aes(x=S7_BIN)) + geom_histogram()
ggplot(rf_prob,aes(x=S2_BIN)) + geom_histogram()
ggplot(rf_prob,aes(x=S5_BIN)) + geom_histogram()
ggplot(rf_prob,aes(x=S6_BIN)) + geom_histogram()