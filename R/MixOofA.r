add.element = function(i,x,a)
{
  if(i == 1) x = c(a, x) else if (i < (length(x) + 1)) x = c(x[1:(i-1)],a,x[i:length(x)])
  else x = c(x,a)
  return(x)
}

add.element.everywhere = function(x,a)
{
  t(sapply((1:(length(x)+1)),add.element,x,a))
}

oofa.oa = function(design)
{
  m = ncol(design)
  dt = apply(as.matrix(design), 1, add.element.everywhere, a = (m+1), simplify =  FALSE)
  d1 = do.call(rbind, lapply(dt, function(mat) mat[1:nrow(mat),]))
  return(d1)
}

library(doofa)
PWO = function(design)
  t(apply(design, 1, pwo)) 

D_effi_pwo <- function(X)
{
  n = nrow(X)
  X1 <- matrix(1,n,1)
  q <- ncol(X) + 1
  pwomodel <- as.matrix(cbind(X1,X),n,q)
  xpx <- t(pwomodel)%*%pwomodel
  dt <- det(xpx)^(1/q)
  D <- dt/n
  return(D)
}

library(crossdes)
is_prime <- function(n) {
  if (n <= 1) {
    return(FALSE)
  }
  if (n <= 3) {
    return(TRUE)
  }
  if (n %% 2 == 0 || n %% 3 == 0) {
    return(FALSE)
  }
  i <- 5
  while (i * i <= n) {
    if (n %% i == 0 || n %% (i + 2) == 0) {
      return(FALSE)
    }
    i <- i + 6
  }
  return(TRUE)
}

is_prime_power <- function(n) {
  if (is_prime(n)) {
    return(TRUE)
  }
  for (i in 2:sqrt(n)) {
    if (n %% i == 0 && is_prime(i) && i ^ round(log(n, i)) == n) {
      return(TRUE)
    }
  }
  return(FALSE)
}

COA = function(m)
{
  if (is_prime(m) || is_prime_power(m)) {
    h<-m-1
  } else {
      return("m is not a prime or prime power")
    }
  if(is_prime(m)){
    k<-MOLS(m,1)
  }
  if (is_prime_power(m)){
    prime_factorization <- function(n) {
      factors <- c()
      d <- 2
      while (n > 1) {
        if (n %% d == 0) {
          factors <- c(factors, d)
          n <- n / d
        } else {
            d <- d + 1
          }
      }
      return(factors)
    }
    find_prime_power <- function(number) {
      factors <- prime_factorization(number)
      primes <- unique(factors)
      powers <- numeric(length(primes))
      for (i in seq_along(primes)) {
        powers[i] <- sum(factors == primes[i])
      }
      return(list(primes = primes, powers = powers))
    }
    result <- find_prime_power(m)
    p<-result$primes
    n<-result$powers
    k<-MOLS(p,n)
  }
  if(h == (m-1)){
    coa_mat_tran<-matrix(k,m*(m-1),m)
    split_matrix <- function(matrix, m) {
      if (nrow(matrix) %% m != 0) {
        stop("Number of rows in the matrix is not divisible by m.")
      }
      num_sets <- nrow(matrix) / m
    sets <- vector("list", num_sets)
    for (i in 1:num_sets) {
      start_row <- (i - 1) * m + 1
      end_row <- i * m
      sets[[i]] <- matrix[start_row:end_row, , drop = FALSE]
    }
    return(sets)
  }
    combine_transpose <- function(sets) {
    transposed_sets <- lapply(sets, function(set) t(set))
    combined_matrix <- do.call(rbind, transposed_sets)
    return(combined_matrix)
  }
    sets <- split_matrix(coa_mat_tran, m)
    combined_matrix <- combine_transpose(sets)
  }
  return(combined_matrix)
}

oofa.sld  = function(m)
{
  if(m == 3 | m == 4) k=0 else k=1
  if(k == 0){
    set1<- cbind(diag(1,m,m), matrix(0,m,choose(m, 2)))
    x <- seq(0, 1, by = 1/m)
    if (m==3){
      y <- x[x != 1]
      g1 <- matrix(0,  m*(m-1)/2, m)
    } else {
        a<-c(0.5,1)
        y<-x[!x %in% a]
        y<-c(0,y)
        g1 <- matrix(0,  m, m)
        g1[1, ] <- y
        for (i in 2:nrow(g1) ){
          g1[i, ]<-c(g1[i-1, -1], g1[i-1, 1])
        }
        b<-c(0.5,0.5,0,0,0,0,0.5,0.5)
        b1<-matrix(b, 2, 4, byrow = TRUE)
        g1<-rbind(g1,b1)
    }
    replicate_rows <- function(mat, n) {
      num_rows <- nrow(mat)
      num_cols <- ncol(mat)
      replicated_mat <- matrix(0, nrow = num_rows * n, ncol = num_cols)
      for (i in 1:num_rows) {
        start_index <- (i - 1) * n + 1
        end_index <- i * n
        replicated_mat[start_index:end_index, ] <- rep(mat[i, ], each = n)
      }
      return(replicated_mat)
    }
    g12 <- replicate_rows(g1, 2)
    generate_combination_matrix <- function(input_matrix) {
      combination_matrix <- matrix(0, m*(m-1)/2, choose(m, 2))
      col_counter <- 1
      for (i in 1:(m - 1)) {
        for (j in (i + 1):m) {
          combination_matrix[, col_counter] <- as.integer(input_matrix[, i] != 0 & input_matrix[, j] != 0)
          col_counter <- col_counter + 1
        }
      }
      return(combination_matrix)
    }
    g13<-matrix(NA, m*(m-1), choose(m,2))
    for (t in 1:(m*(m-1)/2)) {
      g13[(2*t-1),]<-generate_combination_matrix(g1)[t,]
      g13[(2*t),]<-(-1)*generate_combination_matrix(g1)[t,]
    }
    set2<-cbind(g12,g13)
    g14<-matrix(1/m,m,m)
    generate_cyclic_latin_square <- function(m) {
      if (m < 1) {
        stop("Order of the Latin square must be a positive integer.")
      }
      latin_square <- matrix(0, nrow = m, ncol = m)
      for (i in 1:m) {
        latin_square[i, ] <- ((i-1):(i + m - 2)) %% m + 1
      }
      return(latin_square)
    }
    P<- generate_cyclic_latin_square(m) 
    generate_Z <- function(P){
      Z <- matrix(nrow = nrow(P),ncol = choose(ncol(P),2))
      for(p in 1:nrow(P)){
        colIndex <- 1
        for(i in 1:(ncol(P)-1)){
          for(j in (i+1):ncol(P)){
            k <- which(P[p,] == i)
            l <- which(P[p,] == j)
            Z[p,colIndex] <- sign(l-k)
            colIndex <- colIndex + 1
          }
        }
      }
      return(Z)
    }
    set3<-cbind(g14, generate_Z(P))
    final_Oofa_SLD<-rbind(set1,set2,set3)
  }else{
    set1<- cbind(diag(1,m,m), matrix(0,m,choose(m, 2)))
    x <- seq(0, 1, by = 1/m)
    y<-c(0, 0, 0, 1/m, 4/m)   
    z<-c(0, 0, 0, 2/m, 3/m)  
    a1 <- matrix(0,  m, m)
    a1[1, ] <- y
    for (i in 2:nrow(a1) ){
      a1[i, ]<-c(a1[i-1, -1], a1[i-1, 1])
    }
    b1 <- matrix(0,  m, m)
    b1[1, ] <- z
    for (i in 2:nrow(b1) ){
      b1[i, ]<-c(b1[i-1, -1], b1[i-1, 1])
    }
    g1<-rbind(a1, b1)
    replicate_rows <- function(mat, n) {
      num_rows <- nrow(mat)
      num_cols <- ncol(mat)
      replicated_mat <- matrix(0, nrow = num_rows * n, ncol = num_cols)
      for (i in 1:num_rows) {
        start_index <- (i - 1) * n + 1
        end_index <- i * n
        replicated_mat[start_index:end_index, ] <- rep(mat[i, ], each = n)
      }
      return(replicated_mat)
    }
    g12 <- replicate_rows(g1, 2)
    generate_combination_matrix <- function(input_matrix) {
      combination_matrix <- matrix(0, m*(m-1)/2, choose(m, 2))
      col_counter <- 1
      for (i in 1:(m - 1)) {
        for (j in (i + 1):m) {
          combination_matrix[, col_counter] <- as.integer(input_matrix[, i] != 0 & input_matrix[, j] != 0)
          col_counter <- col_counter + 1
        }
      }
      return(combination_matrix)
    }
    g13<-matrix(NA, m*(m-1), choose(m,2))
    for (t in 1:(m*(m-1)/2)) {
      g13[(2*t-1),]<-generate_combination_matrix(g1)[t,]
      g13[(2*t),]<-(-1)*generate_combination_matrix(g1)[t,]
    }
    set2<-cbind(g12,g13)
    y<-c(0, 0, 1/m, 1/m, 3/m)   
    z<-c(0, 0, 2/m, 2/m, 1/m)  
    a1 <- matrix(0,  m, m)
    a1[1, ] <- y
    for (i in 2:nrow(a1) ){
      a1[i, ]<-c(a1[i-1, -1], a1[i-1, 1])
    }
    b1 <- matrix(0,  m, m)
    b1[1, ] <- z
    for (i in 2:nrow(b1) ){
      b1[i, ]<-c(b1[i-1, -1], b1[i-1, 1])
    }
    g1<-rbind(a1, b1)
    replicate_rows <- function(mat, n) {
      num_rows <- nrow(mat)
      num_cols <- ncol(mat)
      replicated_mat <- matrix(0, nrow = num_rows * n, ncol = num_cols)
      for (i in 1:num_rows) {
        start_index <- (i - 1) * n + 1
        end_index <- i * n
        replicated_mat[start_index:end_index, ] <- rep(mat[i, ], each = n)
      }
      return(replicated_mat)
    }
    g32 <- replicate_rows(g1, factorial(m-2))
    l=m-2
    generate_full_design <- function(l){
      Plist <- permn(1:l)
      return(matrix(unlist(Plist),byrow=TRUE,nrow=factorial(l)))
    }
    generate_Z <- function(P){
      Z <- matrix(nrow = nrow(P),ncol = choose(ncol(P),2))
      for(p in 1:nrow(P)){
        colIndex <- 1
        for(i in 1:(ncol(P)-1)){
          for(j in (i+1):ncol(P)){
            k <- which(P[p,] == i)
            l <- which(P[p,] == j)
            Z[p,colIndex] <- sign(l-k)
            colIndex <- colIndex + 1
          }
        }
      }
      return(Z)
    }
    generate_Z(generate_full_design(l))
    orders_list <- list()
    for (i in 1:nrow(g1)) {
      non_zero <- which(g1[i, ] != 0)
      orders <- non_zero
      orders_list[[i]] <- orders
    }
    orders_matrix <- do.call(rbind, orders_list)
    P <- matrix(nrow = m, ncol = m, 0) 
    P[lower.tri(P,diag=F)] <- 1:choose(m,2)
    P <- t(P)   
    generate_Z_combinations <- function(orders_matrix, m){ 
      n_combinations <- choose(m, 2)
      n_rows <- nrow(orders_matrix)
      Z_combinations <- matrix(0, nrow = n_rows * 6, ncol = n_combinations)
      for (row in 1:n_rows) {
        order <- orders_matrix[row, ]
        combinations <- combn(order, 2)
        colnums <- c() 
        for(p in 1:ncol(combinations)){
          colnum <- P[combinations[1,p],combinations[2,p]]
          colnums <- c(colnums,colnum)
        }
        Z <- generate_Z(generate_full_design(3))
        start_row <- (row - 1) * 6 + 1
        end_row <- start_row + 5
        Z_combinations[start_row:end_row,colnums] <- Z
      }
      return(Z_combinations)
    }
    Z_combinations <- generate_Z_combinations(orders_matrix, m)
    g33<-Z_combinations
    set3<-cbind(g32,g33)
    g14<-matrix(1/m,m,m)
    generate_cyclic_latin_square <- function(m) {
      if (m < 1) {
        stop("Order of the Latin square must be a positive integer.")
      }
      latin_square <- matrix(0, nrow = m, ncol = m)
      for (i in 1:m) {
        latin_square[i, ] <- ((i-1):(i + m - 2)) %% m + 1
      }
      return(latin_square)
    }
    P<- generate_cyclic_latin_square(m) 
    generate_Z <- function(P){
      Z <- matrix(nrow = nrow(P),ncol = choose(ncol(P),2))
      for(p in 1:nrow(P)){
        colIndex <- 1
        for(i in 1:(ncol(P)-1)){
          for(j in (i+1):ncol(P)){
            k <- which(P[p,] == i)
            l <- which(P[p,] == j)
            Z[p,colIndex] <- sign(l-k)
            colIndex <- colIndex + 1
          }
        }
      }
      return(Z)
    }
    set4<-cbind(g14, generate_Z(P))
    final_Oofa_SLD<-rbind(set1,set2,set3,set4)
  }
  return(final_Oofa_SLD)
}  

library(mixexp)
oofa.scd = function(m)
{
  scd_matrix <- SCD(m)
  divide_and_repeat <- function(scd_matrix, m) {
    group_list <- list()
    for (i in 1:m) {
      group_list[[i]] <- matrix(0, nrow = 0, ncol = ncol(scd_matrix))
    }
    for (i in 1:nrow(scd_matrix)) {
      non_zero_count <- sum(scd_matrix[i, ] != 0)
      group_list[[non_zero_count]] <- rbind(group_list[[non_zero_count]], scd_matrix[i, , drop = FALSE])
    }
    for (i in 1:m) {
      repeat_count <- i
      group_list[[i]] <- group_list[[i]][rep(1:nrow(group_list[[i]]), each = repeat_count), ]
    }
    return(group_list)
  }
  scd_groups <- divide_and_repeat(scd_matrix, m)
  merged_matrix <- do.call(rbind, scd_groups)
  all_results <- list()
  for (i in 2:m) {
    selected_elements <- combinat::combn(1:m, i, simplify = FALSE)
    for (l in seq_along(selected_elements)) {
      set <- selected_elements[[l]]
      n <- length(set)
      result <- matrix(0, nrow = m, ncol = m)
      for (j in 1:n) {
        result[j, ] <- c(set, setdiff(1:m, set))
        set <- c(tail(set, -1), head(set, 1))
      }
      all_results[[length(all_results) + 1]] <- result
    }
  }
  final_result <- do.call(rbind, all_results)
  final_result <- final_result[apply(final_result, 1, function(row) all(row != 0)), ]
  generate_Z <- function(P){
    Z <- matrix(nrow = nrow(P),ncol = choose(ncol(P),2))
    for(p in 1:nrow(P)){
      colIndex <- 1
      for(i in 1:(ncol(P)-1)){
        for(j in (i+1):ncol(P)){
          k <- which(P[p,] == i)
          l <- which(P[p,] == j)
          Z[p,colIndex] <- sign(l-k)
          colIndex <- colIndex + 1
        }
      }
    }
    return(Z)
  }
  generate_combination_matrix <- function(input_matrix) {
    combination_matrix <- matrix(0, nrow(input_matrix), choose(ncol(input_matrix), 2))
    col_counter <- 1
    for (i in 1:(ncol(input_matrix) - 1)) {
      for (j in (i + 1):ncol(input_matrix)) {
        combination_matrix[, col_counter] <- as.integer(input_matrix[, i] != 0 & input_matrix[, j] != 0)
        col_counter <- col_counter + 1
      }
    }
    return(combination_matrix)
  }
  result_matrix<-cbind(merged_matrix,generate_combination_matrix(merged_matrix)*(rbind(matrix(1,m,choose(m,2)),generate_Z(final_result))))
  colnames(result_matrix)[(ncol(merged_matrix) + 1):ncol(result_matrix)] <- apply(combn(1:ncol(merged_matrix), 2), 2, function(x) paste0("x", x[1], x[2]))
  rownames(result_matrix) <- 1:nrow(result_matrix)
  final_Oofa_SCD<-round(result_matrix, 2)
  return(final_Oofa_SCD)
}

library(Rsolnp)

mixoofa.anova<-function(formula,response,nmix,mixvar,Zmat,caption){
  m <- nmix
  X <- model.matrix(formula,data=mixvar)
  PX <- X%*%solve(t(X)%*%X)%*%t(X)
  Z <- Zmat
  Z<-as.matrix(Z)
  PZ <- Z%*%solve(t(Z)%*%Z)%*%t(Z)
  PD <- PX + PZ
  Y <- matrix(response,nrow=length(response),ncol=1)
  SSM <- t(Y)%*%PX%*%Y
  SSO <- t(Y)%*%PZ%*%Y
  SSE <- t(Y)%*%(diag(nrow(PD))-PD)%*%Y
  dfm <- sum(diag(PX))
  dfo <- sum(diag(PZ))
  dfe <- sum(diag(diag(nrow(PD))-PD))
  SS <- c(SSM,SSO,SSE)
  df <- c(dfm,dfo,dfe)
  MS <- SS/df
  Fstat <- c((SSM/dfm)/(SSE/dfe),(SSO/dfo)/(SSE/dfe),NA)
  pvalue <- c(pf(Fstat[1],dfm,dfe,lower.tail=FALSE),pf(Fstat[2],dfo,dfe,lower.tail=FALSE),NA)
  pvalue <- formatC(pvalue,format="e",digits=4)
  pvalue[3] <- ""
  DFMAT <- cbind(SS,df,MS,Fstat)
  DFMAT <- round(DFMAT,4)
  DFMAT <- cbind(DFMAT,pvalue)
  Source <- c("Mixture","Order","Error")
  DFMAT <- cbind(Source,DFMAT)
  datframe <- data.frame(DFMAT)
  if(missing(caption)){
    # print(datframe)
    return(datframe)
  }
  else{
    # print(datframe)
    return(datframe)
  }
}
find_optimum_mixture_target <- function(model,z,m,target){
  zvec <- z
  modmat <- model.matrix(model)
  X <- modmat[,1:m]
  xColNames <- colnames(X)
  zColNames <- c()
  for(j in 1:m){
    for(k in 1:m){
      if(j < k){
        zColName <- paste("z",j,k,sep="")
        zColNames <- c(zColNames,zColName)
      }
    }
  }
  opt_func <- function(x) {
    newdat <- as.data.frame(matrix(c(x,zvec),nrow=1,ncol=m + choose(m,2)))
    colnames(newdat) <- c(xColNames,zColNames)
    return((predict(model,newdat) - target)^2)
  }
  equal <- function(x) {
    sum(x) 
  }
  solnp(rep(1/m,m), 
        opt_func, 
        eqfun=equal,  
        eqB=1,   
        LB = rep(0.001,m), 
        UB = rep(1,m), 
        control = list(trace=0) 
  )
}
generate_full_design <- function(m){
  Plist <- permn(1:m) 
  return(matrix(unlist(Plist),byrow=TRUE,nrow=factorial(m)))
}
generate_Z <- function(P){
  Z <- matrix(nrow = nrow(P),ncol = choose(ncol(P),2))
  for(p in 1:nrow(P)){
    colIndex <- 1
    for(i in 1:(ncol(P)-1)){
      for(j in (i+1):ncol(P)){
        k <- which(P[p,] == i)
        l <- which(P[p,] == j)
        Z[p,colIndex] <- sign(l-k)
        colIndex <- colIndex + 1
      }
    }
  }
  return(Z)
}
rep_row<-function(x,n){
  matrix(rep(x,each=n),nrow=n)
}
find_opt_target <- function(m,model,target){
  all_orders <- generate_Z(generate_full_design(m)) 
  for(i in 1:factorial(m)){
    z <- as.vector(all_orders[i,]) 
    x <- find_optimum_mixture_target(model,z,m,target=target)$pars
    newdat <- data.frame(matrix(c(x,z),nrow=1))
    xnames = paste0("x",1:m)
    znames = NULL
    for(u in 1:(m-1)){
      for(u1 in (u+1):m){
        znames = c(znames, paste0("z",u,u1))
      }
    }
    names(newdat) = c(xnames, znames)
    fhat <- as.numeric(predict(model,newdat))
    dist <- (fhat - target)^2
    if(dist < 1e-10){
      # print(c(x,z))
      out = c(x,z)
    }
  }  
  return(out)
}