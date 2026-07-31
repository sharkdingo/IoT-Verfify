package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.dto.verification.SpecResultDto;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/** Shared user-semantic projections for verification tools. */
final class VerificationToolPresenter {

    private VerificationToolPresenter() {
    }

    /** Persistence ids are unnecessary for interpretation and follow-up tools use run/trace ids. */
    static List<Map<String, Object>> specResults(List<SpecResultDto> specResults) {
        if (specResults == null || specResults.isEmpty()) {
            return List.of();
        }
        List<Map<String, Object>> presented = new ArrayList<>(specResults.size());
        for (SpecResultDto specResult : specResults) {
            if (specResult == null) continue;
            Map<String, Object> row = new LinkedHashMap<>();
            row.put("specificationLabel", specResult.getSpecificationLabel());
            row.put("formulaPreview", specResult.getFormulaPreview());
            row.put("formulaKind", specResult.getFormulaKind());
            row.put("outcome", specResult.getOutcome());
            row.put("checkedExpression", specResult.getExpression());
            presented.add(row);
        }
        return List.copyOf(presented);
    }
}
